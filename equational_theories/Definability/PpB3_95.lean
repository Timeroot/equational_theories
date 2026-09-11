import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  clear eq25
  have eq51 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq86 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
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
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq83
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq83
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq83
       grind)
    | exact superpose eq83 eq16
    | exact resolve eq16 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq94
    | exact resolve eq94 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq101 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 X1) ∨ (k (M.op (M.op X1 X0) (M.op X1 X0)) X1) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X1 X1) (M.op X1 X0)
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq299 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq305 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq303
    | exact resolve eq303 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq307 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq299
       have i₂ := eq53 sF4 sF4
       grind)
    | exact superpose eq53 eq299
    | exact resolve eq299 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq309 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq296
       have i₂ := eq53 sF0 sF0
       grind)
    | exact superpose eq53 eq296
    | exact resolve eq296 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq310 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq294
    | exact resolve eq294 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq311 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq293 X0 X1
       have i₂ := eq53 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq293
    | exact resolve eq293 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq312 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq305
    | exact resolve eq305 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq315 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq310
    | exact resolve eq310 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq316 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq311 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq311
    | exact resolve eq311 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq321 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq301 (M.op X0 X0) X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq301
    | exact resolve eq301 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq307 eq53
    | exact resolve eq53 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq613
       have i₂ := eq53 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq53 eq613
    | exact resolve eq613 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq620 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq618
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq618
    | exact resolve eq618 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq621 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq620
       have i₂ := eq53 sF3 sF3
       grind)
    | exact superpose eq53 eq620
    | exact resolve eq620 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq622 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) ∨ X0 ≠ X1 ∨ (k (M.op (M.op X1 X0) (M.op X1 X0)) X1) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq101
    | (have j0 := eq101 X0 X1
       grind)
    | (have r₁ := eq101 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 (M.op X0 X0))
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq101 (M.op X1 (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq101 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq623 : ∀ X0 X1 : G, (k (M.op (M.op X1 X0) (M.op X1 X0)) X1) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) ∨ (M.op X1 X1) = (M.op X1 (M.op X0 X0)) ∨ X0 ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq622 X0 X1
       have i₂ := eq53 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq622
    | (have j0 := eq622 X0 X1
       grind)
    | (have r₁ := eq622 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 (M.op X0 X0))
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq622 (M.op X1 (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq622 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq624 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (M.op X1 (M.op X0 X0)) ∨ (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) = (k (M.op X1 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq623 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq623
    | (have j0 := eq623 X0 X1
       grind)
    | (have r₁ := eq623 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 (M.op X0 X0))
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq623 (M.op X1 (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq623 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq625 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq621 eq301
    | exact resolve eq301 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq309 eq53
    | exact resolve eq53 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : x ≠ (M.op y y) ∨ (M.op x x) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) = (k (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) x) := by
    first
    | exact superpose eq309 eq12
    | (have j0 := eq12 (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) x
       grind)
    | exact resolve eq12 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : (k (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) x) = (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) ∨ x ≠ (M.op y y) ∨ (M.op x x) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq639
       have i₂ := eq53 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq53 eq639
    | exact resolve eq639 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq643 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq638
       have i₂ := eq53 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq53 eq638
    | exact resolve eq638 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq644 : (M.op x y) = (k (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) x) ∨ x ≠ (M.op y y) ∨ (M.op x x) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq642
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq642
    | exact resolve eq642 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq645 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq643
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq643
    | exact resolve eq643 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq646 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq645
       have i₂ := eq53 y y
       grind)
    | exact superpose eq53 eq645
    | exact resolve eq645 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq647 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have j0 := eq624 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq648 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq301 y y
       have i₂ := eq646
       grind)
    | exact superpose eq646 eq301
    | exact resolve eq301 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq321 (M.op X0 X0)
       have i₂ := eq301 (M.op X0 X0) X0
       grind)
    | exact superpose eq301 eq321
    | exact resolve eq321 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq621 eq321
    | exact resolve eq321 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq663 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq663
    | exact resolve eq663 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq2624 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq312 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq312
    | exact resolve eq312 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2699 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2624 X0 X1
       have i₂ := eq301 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq301 eq2624
    | exact resolve eq2624 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2624
  have eq2836 : (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) = (M.op x (M.op y (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))))) := by
    first
    | exact superpose eq51 eq316
    | exact resolve eq316 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2867 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq316 X0 X1
       grind)
    | exact superpose eq316 eq53
    | exact resolve eq53 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq2873 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2867 X0 X1
       have i₂ := eq53 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq2867
    | exact resolve eq2867 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2867
  have eq2899 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op x (M.op y (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))))) := by
    first
    | (have i₁ := eq2836
       have i₂ := eq53 sF0 sF0
       grind)
    | exact superpose eq53 eq2836
    | exact resolve eq2836 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2836
  have eq2914 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2873 X0 X1
       have i₂ := eq53 (M.op X0 X0) X1
       grind)
    | exact superpose eq53 eq2873
    | exact resolve eq2873 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873
  have eq2934 : (M.op x (M.op y (M.op y y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq309 eq2899
    | exact resolve eq2899 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq2899
  have eq2948 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2914 X0 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq2914
    | exact resolve eq2914 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2914
  have eq2959 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq2934
       have i₂ := eq646
       grind)
    | exact superpose eq646 eq2934
    | exact resolve eq2934 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq2934
  have eq2970 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2948 X0 X1
       have i₂ := eq312 X1 X0
       grind)
    | exact superpose eq312 eq2948
    | exact resolve eq2948 eq312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq2948
  have eq3018 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2970 X1 X2
       have i₂ := eq2970 X1 X0
       grind)
    | (have i₁ := eq2970 X0 X1
       have i₂ := eq2970 X0 X0
       grind)
    | exact superpose eq2970 eq2970
    | exact resolve eq2970 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3486 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq304 X0 X1
       have i₂ := eq315 X0 X1
       grind)
    | exact superpose eq315 eq304
    | exact resolve eq304 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq3652 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = (k (M.op X0 (M.op X0 X1)) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3486 X0 X0
       have i₂ := eq2970 X0 X1
       grind)
    | (have i₁ := eq3486 X0 X0
       have i₂ := eq2970 X0 X0
       grind)
    | exact superpose eq2970 eq3486
    | exact resolve eq3486 eq2970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2970
  have eq3706 : (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))))) = (k (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq307 eq3486
    | exact resolve eq3486 eq307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq3486
  have eq3720 : (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))))) = (k (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq3706
       have i₂ := eq53 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq53 eq3706
    | exact resolve eq3706 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3706
  have eq3772 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3652 X0 X1
       have i₂ := eq2699 X1 X0
       grind)
    | exact superpose eq2699 eq3652
    | exact resolve eq3652 eq2699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2699 eq3652
  have eq3779 : (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3720
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq3720
    | exact resolve eq3720 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq3826 : (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq3779
       have i₂ := eq671 sF4
       grind)
    | exact superpose eq671 eq3779
    | exact resolve eq3779 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq3779
  have eq3860 : (σ y) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq52 eq3826
    | exact resolve eq3826 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3826
  have eq4545 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq648 eq3018
    | exact resolve eq3018 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq4556 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq625 eq3018
    | exact resolve eq3018 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq3018
  have eq5571 : ∀ X0 : G, (σ X0) ≠ (σ (k y X0)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq86 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq7080 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = (M.op X0 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq647 X0
       have i₂ := eq315 X0 X0
       grind)
    | exact superpose eq315 eq647
    | (have j0 := eq647 X0
       grind)
    | exact resolve eq647 eq315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315 eq647
  have eq7081 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7080 X0
       have i₂ := eq301 X0 X0
       grind)
    | exact superpose eq301 eq7080
    | (have j0 := eq7080 X0
       grind)
    | exact resolve eq7080 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7080
  have eq11546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11546
    | exact resolve eq11546 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11546
  have eq11554 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11547
       have r₂ := eq28
       grind)
    | exact resolve eq11547 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11547
  have eq11556 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11554
    | exact resolve eq11554 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11554
  have eq11558 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11556
  have eq11607 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11558
    | exact resolve eq11558 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11558
  have eq12172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11607 eq96
    | exact resolve eq96 eq11607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11607
  have eq12180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12172
  have eq12182 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12180
       have r₂ := eq28
       grind)
    | exact resolve eq12180 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12180
  have eq12292 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12182
  have eq12341 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12292
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12292
    | exact resolve eq12292 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12292
  have eq13037 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq12341
       grind)
    | exact superpose eq12341 eq83
    | exact resolve eq83 eq12341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12341
  have eq13059 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq13037
    | exact resolve eq13037 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13037
  have eq13446 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13059 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq13059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13446
    | exact resolve eq13446 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13446
  have eq13456 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13449
       have r₂ := eq28
       grind)
    | exact resolve eq13449 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13449
  have eq13458 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13456
    | exact resolve eq13456 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13456
  have eq13459 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13458
  have eq13489 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13459
  have eq13538 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13489
    | exact resolve eq13489 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13489
  have eq13784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13538 eq13059
    | exact resolve eq13059 eq13538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13059 eq13538
  have eq13790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13784
  have eq13794 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13790
       have r₂ := eq28
       grind)
    | exact resolve eq13790 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13790
  have eq13797 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13794 eq28
    | exact resolve eq28 eq13794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13798 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13794 eq52
    | exact resolve eq52 eq13794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq13812 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13794 eq4556
    | exact resolve eq4556 eq13794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556
  have eq13814 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13812 x
       have i₂ := eq301 x sF2
       grind)
    | exact superpose eq301 eq13812
    | exact resolve eq13812 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13812
  have eq13823 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13814 eq665
    | exact resolve eq665 eq13814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq13825 : (σ y) = (k (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13814 eq3860
    | exact resolve eq3860 eq13814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3860
  have eq13830 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13814 eq301
    | exact resolve eq301 eq13814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13876 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13798 eq7081
    | exact resolve eq7081 eq13798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7081
  have eq13887 : (σ x) = (k (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13798 eq3772
    | exact resolve eq3772 eq13798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3772 eq13798
  have eq14080 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13823 eq53
    | exact resolve eq53 eq13823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq13823
  have eq14106 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14080
       have i₂ := eq14 sF4 sF2
       grind)
    | exact superpose eq14 eq14080
    | exact resolve eq14080 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14080
  have eq14372 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14106 eq321
    | exact resolve eq321 eq14106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq14106
  have eq70227 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13876 eq13830
    | exact resolve eq13830 eq13876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13830 eq13876
  have eq70264 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq70227
  have eq70336 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq70264
    | exact resolve eq70264 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70264
  have eq70358 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70336 eq93
    | exact resolve eq93 eq70336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70359 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70336 eq96
    | exact resolve eq96 eq70336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70336
  have eq70380 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq70359
  have eq70389 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq70380
       have r₂ := eq13797
       grind)
    | exact resolve eq70380 eq13797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13797 eq70380
  have eq70390 : x = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq70358
    | exact resolve eq70358 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70358
  have eq70397 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq70389
  have eq70461 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70397
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70397
    | exact resolve eq70397 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70397
  have eq72999 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70390
       have i₂ := eq70461
       grind)
    | exact superpose eq70461 eq70390
    | exact resolve eq70390 eq70461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70390 eq70461
  have eq73006 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq72999
  have eq73040 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73006 eq28
    | exact resolve eq28 eq73006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73069 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73006 eq13794
    | exact resolve eq13794 eq73006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13794
  have eq73097 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73006 eq14372
    | exact resolve eq14372 eq73006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14372 eq73006
  have eq73418 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq73097
  have eq73446 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq73069
  have eq73523 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq621 eq73418
    | exact resolve eq73418 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq73418
  have eq73649 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73446 eq13814
    | exact resolve eq13814 eq73446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13814 eq73446
  have eq74004 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq73649
  have eq77044 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73523 eq13825
    | exact resolve eq13825 eq73523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13825 eq73523
  have eq77122 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq77044
  have eq81413 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74004 eq13887
    | exact resolve eq13887 eq74004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13887 eq74004
  have eq81521 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq81413
  have eq85196 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq77122 eq96
    | exact resolve eq96 eq77122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq77122
  have eq85214 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq85196
  have eq85223 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq85214
       have r₂ := eq73040
       grind)
    | exact resolve eq85214 eq73040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73040 eq85214
  have eq95125 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq81521 eq93
    | exact resolve eq93 eq81521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq81521
  have eq95166 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq95125
    | exact resolve eq95125 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq95125
  have eq98018 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq85223
  have eq98086 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98018
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98018
    | exact resolve eq98018 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98018
  have eq102868 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95166
       have i₂ := eq98086
       grind)
    | exact superpose eq98086 eq95166
    | exact resolve eq95166 eq98086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95166 eq98086
  have eq102880 : x = (M.op x y) := by grind
  clear eq102868
  have eq102922 : (M.op x y) = (k (M.op x (M.op x (M.op x y))) x) ∨ x ≠ (M.op y y) ∨ (M.op x x) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2959 eq644
    | exact resolve eq644 eq2959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq102923 : (M.op x x) = (M.op x (M.op x (M.op x y))) ∨ (M.op x y) = (k (M.op x (M.op x (M.op x y))) x) ∨ x ≠ (M.op y y) := by
    first
    | exact superpose eq2959 eq102922
    | exact resolve eq102922 eq2959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2959 eq102922
  have eq102924 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq102880 eq21
    | exact resolve eq21 eq102880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq102926 : y = (M.op x (M.op x x)) := by
    first
    | exact superpose eq102880 eq51
    | exact resolve eq51 eq102880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq103075 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x x))) := by
    intro X0
    first
    | exact superpose eq102880 eq4545
    | exact resolve eq4545 eq102880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4545
  have eq103082 : x = (M.op y y) := by
    first
    | (have i₁ := eq103075 x
       have i₂ := eq301 x x
       grind)
    | exact superpose eq301 eq103075
    | exact resolve eq103075 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq103075
  have eq103216 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq102924
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq102924
    | exact resolve eq102924 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102924
  have eq103219 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq103216 eq27
    | exact resolve eq27 eq103216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112673 : (M.op x x) = (M.op x (M.op x (M.op x y))) ∨ (M.op x y) = (k (M.op x (M.op x (M.op x y))) x) := by
    first
    | (have r₁ := eq102923
       have r₂ := eq103082
       grind)
    | exact resolve eq102923 eq103082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102923 eq103082
  have eq112674 : (M.op x x) = (M.op x (M.op x x)) ∨ (M.op x y) = (k (M.op x (M.op x (M.op x y))) x) := by
    first
    | exact superpose eq102880 eq112673
    | exact resolve eq112673 eq102880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112673
  have eq112675 : y = (M.op x x) ∨ (M.op x y) = (k (M.op x (M.op x (M.op x y))) x) := by
    first
    | (have i₁ := eq112674
       have i₂ := eq102926
       grind)
    | exact superpose eq102926 eq112674
    | exact resolve eq112674 eq102926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112674
  have eq112676 : x = (k (M.op x (M.op x x)) x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq102880 eq112675
    | exact resolve eq112675 eq102880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112675
  have eq112677 : y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq112676
       have i₂ := eq102926
       grind)
    | exact superpose eq102926 eq112676
    | exact resolve eq112676 eq102926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102926 eq112676
  have eq112686 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq112677
  have eq112771 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq112686
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112686
    | exact resolve eq112686 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq112686
  have eq112812 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq102880 eq112771
    | exact resolve eq112771 eq102880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102880 eq112771
  have eq112813 : x = (k y x) := by grind
  clear eq112812
  have eq112845 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq83
       have i₂ := eq112813
       grind)
    | exact superpose eq112813 eq83
    | exact resolve eq83 eq112813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq112865 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5571 x
       have i₂ := eq112813
       grind)
    | exact superpose eq112813 eq5571
    | (have j0 := eq5571 x
       grind)
    | exact resolve eq5571 eq112813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5571 eq112813
  have eq112876 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq112865
  have eq112892 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq112876
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq112876
    | exact resolve eq112876 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112876
  have eq112908 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq103216 eq112845
    | exact resolve eq112845 eq103216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112845
  have eq112916 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq112892
    | exact resolve eq112892 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq112892
  have eq112932 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq112908
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq112908
    | exact resolve eq112908 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112908
  have eq112939 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq103216 eq112916
    | exact resolve eq112916 eq103216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112916
  have eq112954 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq103216 eq112932
    | exact resolve eq112932 eq103216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112932
  have eq112959 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq112939
       have r₂ := eq28
       grind)
    | exact resolve eq112939 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112939
  have eq112967 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq112959
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq112959
    | exact resolve eq112959 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq112959
  have eq112974 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq103216 eq112967
    | exact resolve eq112967 eq103216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103216 eq112967
  have eq113039 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq112974
  have eq113119 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq103219 eq113039
    | exact resolve eq113039 eq103219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103219 eq113039
  have eq113128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq112954 eq113119
    | exact resolve eq113119 eq112954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112954 eq113119
  have eq113131 : False := by grind
  exact eq113131

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyy_pxx_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq65 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq73 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq19
  have eq74 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq73
    | (have j0 := eq73 X0
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq78 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq9
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq78 (M.op X0 X1) X2
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq78
    | exact resolve eq78 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq78 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq78 X0 (M.op X0 X0)
       grind)
    | exact superpose eq78 eq78
    | exact resolve eq78 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq78 X0 (M.op X0 X0)
       grind)
    | exact superpose eq78 eq83
    | exact resolve eq83 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 X0 X1
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq107
    | exact resolve eq107 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq107
  have eq147 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq83 X1 X1 X2
       have i₂ := eq131 X1 X0
       grind)
    | (have i₁ := eq83 X0 X0 X2
       have i₂ := eq131 X0 X0
       grind)
    | exact superpose eq131 eq83
    | exact resolve eq83 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq131
  have eq1196 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1555 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq10
    | (have j1 := eq66 X0
       grind)
    | exact resolve eq10 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq6633 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1196 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq1196
    | (have j0 := eq1196 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq1196 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6640 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq1196
  have eq10155 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq10
    | (have j1 := eq74 X0
       grind)
    | exact resolve eq10 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq12605 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op X1 (M.op X1 (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq147 (σ (M.op X0 X0)) (σ X0) X1
       have i₂ := eq6640 X0
       grind)
    | exact superpose eq6640 eq147
    | (have j1 := eq6640 X0
       grind)
    | exact resolve eq147 eq6640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq6640
  have eq12657 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12605 X0 x
       have i₂ := eq78 (σ (M.op X0 X0)) x
       grind)
    | exact superpose eq78 eq12605
    | (have j0 := eq12605 X0 x
       grind)
    | exact resolve eq12605 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq12605
  have eq12658 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12657 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12657
  have eq12680 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12658
  have eq12725 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6633 x y
       grind)
    | exact superpose eq6633 eq16
    | (have j1 := eq6633 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6633 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq6633 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq6633 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq6633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6633
  have eq12771 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq12725
  have eq14793 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq85 (σ X0)
       have i₂ := eq12680 X0
       grind)
    | exact superpose eq12680 eq85
    | (have j1 := eq12680 X0
       grind)
    | exact resolve eq85 eq12680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31409 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq10155 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10155
  have eq31430 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31409 (σ X0)
       have i₂ := eq31 X0 (σ X0)
       grind)
    | exact superpose eq31 eq31409
    | (have j0 := eq31409 (σ X0)
       grind)
    | exact resolve eq31409 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq31409
  have eq31431 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31430 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31430
    | (have j0 := eq31430 X0
       grind)
    | exact resolve eq31430 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31430
  have eq31434 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31431 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq31431
    | (have j0 := eq31431 X0
       grind)
    | exact resolve eq31431 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31431
  have eq31439 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq31434 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq31434
    | (have j0 := eq31434 (σ X0)
       grind)
    | exact resolve eq31434 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31434
  have eq198101 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1555 y
       have i₂ := eq12771
       grind)
    | exact superpose eq12771 eq1555
    | exact resolve eq1555 eq12771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555 eq12771
  have eq198328 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq198101
  have eq198362 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq198328
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq198328
    | exact resolve eq198328 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198328
  have eq198377 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  have eq198397 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq198377
  have eq198411 : y = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq198397
  have eq198755 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq198362 eq198411
    | exact resolve eq198411 eq198362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198362 eq198411
  have eq198756 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq198755
  have eq198921 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq85 y
       have i₂ := eq198756
       grind)
    | exact superpose eq198756 eq85
    | exact resolve eq85 eq198756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq198964 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14793 y
       have i₂ := eq198756
       grind)
    | exact superpose eq198756 eq14793
    | exact resolve eq14793 eq198756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14793 eq198756
  have eq199125 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq198964
  have eq201663 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq199125
       grind)
    | exact superpose eq199125 eq16
    | exact resolve eq16 eq199125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199125
  have eq201886 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq198921 eq201663
    | exact resolve eq201663 eq198921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198921 eq201663
  have eq201887 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq201886
  have eq201913 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq201887
       grind)
    | exact superpose eq201887 eq10
    | exact resolve eq10 eq201887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201887
  have eq202054 : x = y ∨ x = y := by
    first
    | (have i₁ := eq201913
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq201913
    | exact resolve eq201913 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201913
  have eq202055 : x = y := by grind
  clear eq202054
  have eq202056 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq202055
       grind)
    | exact superpose eq202055 eq16
    | exact resolve eq16 eq202055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202055
  have eq202057 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq202056
       have i₂ := eq12680 x
       grind)
    | exact superpose eq12680 eq202056
    | (have j1 := eq12680 x
       grind)
    | (have r₁ := eq202056
       have r₂ := eq12680 x
       grind)
    | exact resolve eq202056 eq12680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12680
  have eq202062 : (σ x) = (σ (M.op x x)) := by grind
  clear eq202057
  have eq202063 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq202056
       have i₂ := eq202062
       grind)
    | exact superpose eq202062 eq202056
    | exact resolve eq202056 eq202062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202056
  have eq202065 : (τ (σ x)) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq202062
       grind)
    | exact superpose eq202062 eq10
    | exact resolve eq10 eq202062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202062
  have eq202212 : x = (M.op x x) := by
    first
    | (have i₁ := eq202065
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq202065
    | exact resolve eq202065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202065
  have eq202213 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
  clear eq202063
  have eq202222 : x = (k x x) := by grind
  clear eq202212
  have eq202684 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq31439 x
       have i₂ := eq202222
       grind)
    | exact superpose eq202222 eq31439
    | (have j0 := eq31439 x
       grind)
    | exact resolve eq31439 eq202222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31439 eq202222
  have eq202699 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq202684
  have eq202707 : False := by grind
  exact eq202707

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq61 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 X1) X2
       have i₂ := eq61 X1 X0
       grind)
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 (M.op X0 X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq62
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq62 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq68 (M.op X0 X0)
       have i₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq68
    | exact resolve eq68 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq76 X0
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq76
    | exact resolve eq76 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq91 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq62 X0 (M.op X0 X0)
       grind)
    | exact superpose eq62 eq67
    | exact resolve eq67 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq91
    | exact resolve eq91 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq126 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 X1 X2
       have i₂ := eq115 X1 X0
       grind)
    | (have i₁ := eq115 X0 X1
       have i₂ := eq115 X0 X0
       grind)
    | exact superpose eq115 eq115
    | exact resolve eq115 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X1 X1 X2
       have i₂ := eq115 X1 X0
       grind)
    | (have i₁ := eq67 X0 X0 X2
       have i₂ := eq115 X0 X0
       grind)
    | exact superpose eq115 eq67
    | exact resolve eq67 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq132 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 X1
       have i₂ := eq115 X1 X0
       grind)
    | (have i₁ := eq62 X0 X0
       have i₂ := eq115 X0 X0
       grind)
    | exact superpose eq115 eq62
    | exact resolve eq62 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1
       have i₂ := eq115 X1 X0
       grind)
    | (have i₁ := eq79 X0
       have i₂ := eq115 X0 X0
       grind)
    | exact superpose eq115 eq79
    | exact resolve eq79 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq137 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1
       have i₂ := eq115 X1 X0
       grind)
    | (have i₁ := eq68 X0
       have i₂ := eq115 X0 X0
       grind)
    | exact superpose eq115 eq68
    | exact resolve eq68 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq115
  have eq251 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq132 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq136 X1 X0
       grind)
    | exact superpose eq136 eq132
    | exact resolve eq132 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq69 X0
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq355 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq360 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq357
    | (have j0 := eq357 X0
       grind)
    | exact resolve eq357 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq368 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq360 X0
       have j1 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq360 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq360 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq404 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131 X1 X2 X1
       have i₂ := eq126 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq131 X1 X2 X1
       have i₂ := eq126 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq126 eq131
    | exact resolve eq131 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq581 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X0))) = (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131 X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) X2
       have i₂ := eq251 X0 X1
       grind)
    | exact superpose eq251 eq131
    | exact resolve eq131 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq588 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq581 X0 X1 X2
       have i₂ := eq61 (M.op X0 X0) (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq61 eq581
    | exact resolve eq581 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq609 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq588 X0 X1 X2
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq588
    | exact resolve eq588 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq622 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq609 X0 X1 x
       have i₂ := eq62 X0 x
       grind)
    | exact superpose eq62 eq609
    | exact resolve eq609 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq831 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq368 (M.op X0 (M.op X0 X0))
       have i₂ := eq622 X0 X0
       grind)
    | exact superpose eq622 eq368
    | exact resolve eq368 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq622
  have eq853 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq831 X0
       have i₂ := eq136 X0 X0
       grind)
    | exact superpose eq136 eq831
    | exact resolve eq831 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq831
  have eq937 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq853 (M.op X1 (M.op X1 X0))
       have i₂ := eq131 X1 X0 (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq131 eq853
    | exact resolve eq853 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq942 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq937 X0 X1
       have i₂ := eq61 (M.op X1 X0) X1
       grind)
    | exact superpose eq61 eq937
    | exact resolve eq937 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq946 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq942 X0 X1
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq942
    | exact resolve eq942 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq948 : ∀ X0 X1 : G, (k (M.op X1 (M.op X1 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq946 X0 X1
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq946
    | exact resolve eq946 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq1039 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op (M.op X0 X0) X0) (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq948 (M.op X1 (M.op X1 X0)) (M.op X0 X0)
       have i₂ := eq137 X1 X0
       grind)
    | exact superpose eq137 eq948
    | exact resolve eq948 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq948
  have eq1070 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op (M.op X0 X0) X0) (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X0 X1
       have i₂ := eq61 (M.op X1 X0) X1
       grind)
    | exact superpose eq61 eq1039
    | exact resolve eq1039 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1084 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op (M.op X0 X0) X0) (M.op X1 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1070 X0 X1
       have i₂ := eq61 X0 X1
       grind)
    | exact superpose eq61 eq1070
    | exact resolve eq1070 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1070
  have eq1095 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1084 X0 X1
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq1084
    | exact resolve eq1084 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1103 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1095 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq1095
    | exact resolve eq1095 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1095
  have eq1106 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1106 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1106
    | (have j0 := eq1106 (σ X0) (σ X1)
       grind)
    | exact resolve eq1106 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1518 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1309 X1 X0
       have i₂ := eq1106 X1 X0
       grind)
    | exact superpose eq1106 eq1309
    | (have j0 := eq1309 X1 X0
       have j1 := eq1106 (σ X1) (σ X0)
       grind)
    | exact resolve eq1309 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12113 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1518 x y
       grind)
    | exact superpose eq1518 eq16
    | (have j1 := eq1518 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1518 x y
       grind)
    | exact resolve eq16 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq12182 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq12113
  have eq12210 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq131 (σ y) (σ x) X0
       have i₂ := eq12182
       grind)
    | exact superpose eq12182 eq131
    | exact resolve eq131 eq12182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq12182
  have eq12249 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12210 x
       have i₂ := eq62 (σ y) x
       grind)
    | exact superpose eq62 eq12210
    | exact resolve eq12210 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq12210
  have eq12316 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1103 (σ x) (σ x)
       have i₂ := eq12249
       grind)
    | exact superpose eq12249 eq1103
    | exact resolve eq1103 eq12249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12249
  have eq12331 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12316
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12316
    | exact resolve eq12316 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12316
  have eq12351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1106 eq12331
    | (have j1 := eq1106 y x
       grind)
    | exact resolve eq12331 eq1106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1106 eq12331
  have eq12363 : y = (M.op y x) := by
    first
    | (have r₁ := eq12351
       have r₂ := eq16
       grind)
    | exact resolve eq12351 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12351
  have eq12385 : ∀ X0 : G, (M.op x x) = (M.op y (M.op X0 (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq404 X0 y x
       have i₂ := eq12363
       grind)
    | exact superpose eq12363 eq404
    | exact resolve eq404 eq12363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12363
  have eq12411 : y = (M.op x x) := by
    first
    | (have i₁ := eq12385 x
       have i₂ := eq132 x y
       grind)
    | exact superpose eq132 eq12385
    | exact resolve eq12385 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12385
  have eq12471 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1103 x x
       have i₂ := eq12411
       grind)
    | exact superpose eq12411 eq1103
    | exact resolve eq1103 eq12411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12411
  have eq13305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1309 y x
       have i₂ := eq12471
       grind)
    | exact superpose eq12471 eq1309
    | (have j0 := eq1309 y x
       grind)
    | exact resolve eq1309 eq12471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq13306 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq13305
       have r₂ := eq16
       grind)
    | exact resolve eq13305 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13305
  have eq13444 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ y) (M.op X0 (M.op X0 (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq404 X0 (σ y) (σ x)
       have i₂ := eq13306
       grind)
    | exact superpose eq13306 eq404
    | exact resolve eq404 eq13306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq13306
  have eq13469 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13444 x
       have i₂ := eq132 x (σ y)
       grind)
    | exact superpose eq132 eq13444
    | exact resolve eq13444 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq13444
  have eq13543 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1103 (σ x) (σ x)
       have i₂ := eq13469
       grind)
    | exact superpose eq13469 eq1103
    | exact resolve eq1103 eq13469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq13469
  have eq13558 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq13543
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq13543
    | exact resolve eq13543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13543
  have eq13580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13558
       have i₂ := eq12471
       grind)
    | exact superpose eq12471 eq13558
    | exact resolve eq13558 eq12471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12471 eq13558
  have eq13592 : False := by grind
  exact eq13592

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq9
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq167 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (k X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 (M.op X1 X0) X1
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq167 (M.op X0 X0) X1
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq167
    | (have j0 := eq167 X0 X0
       have j1 := eq67 X0 X1
       grind)
    | exact resolve eq167 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq167
  have eq1016 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq997 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997
  have eq1020 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1016 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1016 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1016 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1016
  have eq2808 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1020 X0 (τ X1)
       grind)
    | exact superpose eq1020 eq17
    | exact resolve eq17 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq2816 : ∀ X0 X1 : G, (σ (M.op X0 (τ X1))) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2808 X0 X1
       have i₂ := eq1020 (σ X0) X1
       grind)
    | exact superpose eq1020 eq2808
    | exact resolve eq2808 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq2808
  have eq3034 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2816 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2816
    | exact resolve eq2816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2816
  have eq3653 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3034 y x
       grind)
    | exact superpose eq3034 eq16
    | (have r₁ := eq16
       have r₂ := eq3034 y x
       grind)
    | exact resolve eq16 eq3034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3034
  have eq3715 : False := by grind
  exact eq3715

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pyy_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq9
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq124 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (k X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 (M.op X1 X0) X1
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq124 (M.op X0 X0) X1
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq124
    | (have j0 := eq124 X0 X0
       have j1 := eq67 X0 X1
       grind)
    | exact resolve eq124 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq124
  have eq1108 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1090 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1112 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1108 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1108 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1108 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108
  have eq3013 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1112 X0 (τ X1)
       grind)
    | exact superpose eq1112 eq17
    | exact resolve eq17 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq3021 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3013 X0 X1
       have i₂ := eq1112 (σ X0) X1
       grind)
    | exact superpose eq1112 eq3013
    | exact resolve eq3013 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112 eq3013
  have eq3238 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3021 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3021
    | exact resolve eq3021 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021
  have eq4037 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3238 y x
       grind)
    | exact superpose eq3238 eq16
    | (have r₁ := eq16
       have r₂ := eq3238 y x
       grind)
    | exact resolve eq16 eq3238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3238
  have eq4100 : False := by grind
  exact eq4100

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_x_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1
       have i₂ := eq19 (M.op X1 X1) X0
       grind)
    | exact superpose eq19 eq68
    | exact resolve eq68 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq19 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq19 eq67
    | exact resolve eq67 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq19 X1 X1
       grind)
    | exact superpose eq19 eq74
    | exact resolve eq74 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq78 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq78
    | exact resolve eq78 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq78
  have eq82 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq88 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq69 X2 (M.op X0 X1)
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq69
    | exact resolve eq69 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq69 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq69 (M.op X0 X0) X0
       grind)
    | exact superpose eq69 eq69
    | exact resolve eq69 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X1 (σ X0)
       have i₂ := eq82 X0 X0
       grind)
    | exact superpose eq82 eq69
    | (have j1 := eq82 X0 X0
       grind)
    | exact resolve eq69 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq82 X0 X0
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq82 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq82 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq82 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq116 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq113 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq119 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 (M.op X1 (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq118 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq127 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 (M.op X0 X0) X1
       have i₂ := eq69 (M.op X0 X0) X0
       grind)
    | exact superpose eq69 eq79
    | exact resolve eq79 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq127 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq127
    | exact resolve eq127 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq150 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141 X1 X2
       have i₂ := eq141 X1 X0
       grind)
    | (have i₁ := eq141 X0 X1
       have i₂ := eq141 X0 X0
       grind)
    | exact superpose eq141 eq141
    | exact resolve eq141 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X1 X1
       have i₂ := eq141 X1 X0
       grind)
    | (have i₁ := eq69 X0 X0
       have i₂ := eq141 X0 X0
       grind)
    | exact superpose eq141 eq69
    | exact resolve eq69 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 X1 X2
       have i₂ := eq141 X1 X0
       grind)
    | (have i₁ := eq79 X0 X1
       have i₂ := eq141 X0 X0
       grind)
    | exact superpose eq141 eq79
    | exact resolve eq79 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq141
  have eq239 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X1))) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq150 X2 (M.op X3 X1) X3
       have i₂ := eq150 X3 X1 X0
       grind)
    | (have i₁ := eq150 X2 (M.op X3 X1) X3
       have i₂ := eq150 X0 X1 X3
       grind)
    | exact superpose eq150 eq150
    | exact resolve eq150 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) = (M.op X1 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (M.op (M.op X0 X0) (M.op X0 X0)) X0 X1
       have i₂ := eq89 (M.op X0 X0)
       grind)
    | exact superpose eq89 eq88
    | exact resolve eq88 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq355 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq314 X0 x
       have i₂ := eq69 x (M.op X0 X0)
       grind)
    | exact superpose eq69 eq314
    | exact resolve eq314 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq363 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq355 X0
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq355
    | exact resolve eq355 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq374 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq363 X1
       have i₂ := eq150 X1 X1 X0
       grind)
    | (have i₁ := eq363 X1
       have i₂ := eq150 X0 X1 X1
       grind)
    | exact superpose eq150 eq363
    | exact resolve eq363 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq452 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X1))
       have i₂ := eq374 X0 X1
       grind)
    | exact superpose eq374 eq9
    | exact resolve eq9 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq452 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq452
    | exact resolve eq452 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq651 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq158 X1 X2 X1
       have i₂ := eq150 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq158 X1 X2 X1
       have i₂ := eq150 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq150 eq158
    | exact resolve eq158 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (k X3 X2) ∨ (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2)))) ≠ X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq158 X1 X2 X0
       grind)
    | exact superpose eq158 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | exact resolve eq12 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1024 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq471 X1 X2
       have i₂ := eq150 X1 X1 X0
       grind)
    | (have i₁ := eq471 X1 X2
       have i₂ := eq150 X0 X1 X1
       grind)
    | exact superpose eq150 eq471
    | exact resolve eq471 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq1265 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (M.op X3 (M.op X2 (M.op X1 (M.op X1 X0)))))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq651 X3 X2 (M.op X1 (M.op X1 X0))
       have i₂ := eq1024 X1 X0 X1
       grind)
    | exact superpose eq1024 eq651
    | exact resolve eq651 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq2465 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X4 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq239 X4 X2 x X0
       have i₂ := eq239 X1 X2 x X0
       grind)
    | (have i₁ := eq239 X0 X1 X0 X0
       have i₂ := eq239 X0 X1 X2 X0
       grind)
    | exact superpose eq239 eq239
    | exact resolve eq239 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3821 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq107
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq107 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3822 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq3821
  have eq17482 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (M.op X1 (σ (k (τ X0) (τ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq119 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq119
    | exact resolve eq119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq17605 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k (σ (τ X0)) X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17482 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq17482
    | (have j0 := eq17482 X0 X1
       grind)
    | exact resolve eq17482 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17482
  have eq17608 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17605 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17605
    | (have j0 := eq17605 X0 X1
       grind)
    | exact resolve eq17605 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17605
  have eq17687 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 (k X0 X0)) (M.op X1 (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 (k X0 X0)) X1
       have i₂ := eq17608 X0 X1
       grind)
    | exact superpose eq17608 eq19
    | (have j1 := eq17608 X0 X1
       grind)
    | exact resolve eq19 eq17608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17608
  have eq17749 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17687 X0 x
       have i₂ := eq9 (k X0 X0) x
       grind)
    | exact superpose eq9 eq17687
    | (have j0 := eq17687 X0 x
       grind)
    | exact resolve eq17687 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17687
  have eq17771 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq17749 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq17749 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq17749 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17749
  have eq17776 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq17771 X0
       grind)
    | exact superpose eq17771 eq116
    | (have j0 := eq116 X0
       grind)
    | exact resolve eq116 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq17777 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X0 X1
       have i₂ := eq17771 X0
       grind)
    | exact superpose eq17771 eq121
    | (have j0 := eq121 X0 X1
       grind)
    | exact resolve eq121 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq17799 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq17771 (σ X0)
       grind)
    | exact superpose eq17771 eq15
    | exact resolve eq15 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17805 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq17771 (τ X0)
       grind)
    | exact superpose eq17771 eq32
    | exact resolve eq32 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq17823 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17805 X0
       have i₂ := eq17771 X0
       grind)
    | exact superpose eq17771 eq17805
    | exact resolve eq17805 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17805
  have eq17829 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17799 X0
       have i₂ := eq17771 X0
       grind)
    | exact superpose eq17771 eq17799
    | exact resolve eq17799 eq17771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17771 eq17799
  have eq18000 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X1 (τ X0)
       have i₂ := eq17823 X0
       grind)
    | exact superpose eq17823 eq69
    | exact resolve eq69 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18006 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq89 (τ X0)
       have i₂ := eq17823 X0
       grind)
    | exact superpose eq17823 eq89
    | exact resolve eq89 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq18029 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq19 (τ X0) (τ X0)
       have i₂ := eq17823 X0
       grind)
    | exact superpose eq17823 eq19
    | exact resolve eq19 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18068 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (τ X0)))) = (M.op X1 (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2465 X1 X2 (τ X0) (τ X0)
       have i₂ := eq17823 X0
       grind)
    | exact superpose eq17823 eq2465
    | exact resolve eq2465 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2465
  have eq18082 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18029 X0
       have i₂ := eq17823 (M.op X0 X0)
       grind)
    | exact superpose eq17823 eq18029
    | exact resolve eq18029 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18029
  have eq18093 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18082 X0
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq18082
    | exact resolve eq18082 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18082
  have eq18407 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (τ X0))) = (τ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18000 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq1024 X1 X0 X1
       grind)
    | exact superpose eq1024 eq18000
    | exact resolve eq18000 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18000
  have eq19248 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq18006 (M.op X0 (M.op X0 X1))
       have i₂ := eq1024 X0 X1 X0
       grind)
    | exact superpose eq1024 eq18006
    | exact resolve eq18006 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024 eq18006
  have eq20560 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19248 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19248
    | exact resolve eq19248 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20702 : ∀ X0 X1 : G, (τ (M.op X1 (M.op X1 X0))) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ (M.op X1 (M.op X1 X0))) (M.op (τ (M.op X1 (M.op X1 X0))) (τ (M.op X1 (M.op X1 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq471 (τ (M.op X1 (M.op X1 X0))) (τ X0)
       have i₂ := eq19248 X0 X1
       grind)
    | exact superpose eq19248 eq471
    | exact resolve eq471 eq19248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq20743 : ∀ X0 X1 : G, (τ (M.op X1 (M.op X1 X0))) = (M.op (M.op (τ X0) (τ X0)) (M.op (τ (M.op X1 (M.op X1 X0))) (τ (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq20702 X0 X1
       have i₂ := eq18068 (M.op X1 (M.op X1 X0)) (M.op (τ X0) (τ X0)) (τ (M.op X1 (M.op X1 X0)))
       grind)
    | exact superpose eq18068 eq20702
    | exact resolve eq20702 eq18068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18068 eq20702
  have eq20821 : ∀ X0 X1 : G, (τ (M.op X1 (M.op X1 X0))) = (M.op (M.op (τ X0) (τ X0)) (τ (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq20743 X0 X1
       have i₂ := eq18093 (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq18093 eq20743
    | exact resolve eq20743 eq18093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18093 eq20743
  have eq20856 : ∀ X0 X1 : G, (τ (M.op X1 (M.op X1 X0))) = (M.op (M.op (τ X0) (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20821 X0 X1
       have i₂ := eq158 X1 X0 (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq158 eq20821
    | exact resolve eq20821 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20821
  have eq20880 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (τ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20856 X0 X1
       have i₂ := eq17823 X0
       grind)
    | exact superpose eq17823 eq20856
    | exact resolve eq20856 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20856
  have eq20888 : ∀ X0 X1 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (τ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20880 X0 X1
       have i₂ := eq17823 (M.op X0 X0)
       grind)
    | exact superpose eq17823 eq20880
    | exact resolve eq20880 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20880
  have eq20891 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 X0))) = (τ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20888 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq20888
    | exact resolve eq20888 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20888
  have eq20952 : ∀ X0 X1 : G, (M.op (τ (M.op X1 (M.op X1 (σ X0)))) (τ (M.op X1 (M.op X1 (σ X0))))) = (M.op (M.op X0 X0) (τ (M.op X1 (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq374 X0 (τ (M.op X1 (M.op X1 (σ X0))))
       have i₂ := eq20560 X0 X1
       grind)
    | exact superpose eq20560 eq374
    | exact resolve eq374 eq20560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq20971 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) = (τ (M.op X3 (M.op X3 (σ X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1265 (τ (M.op X3 (M.op X3 (σ X0)))) X0 X1 X2
       have i₂ := eq20560 X0 X3
       grind)
    | exact superpose eq20560 eq1265
    | exact resolve eq1265 eq20560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq20983 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X0)) = (τ (M.op X3 (M.op X3 (σ X0)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20971 X0 X1 x X3
       have i₂ := eq88 X1 X0 x
       grind)
    | exact superpose eq88 eq20971
    | exact resolve eq20971 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq20971
  have eq20997 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op X1 (M.op X1 (σ X0))))) = (τ (M.op (M.op X1 (M.op X1 (σ X0))) (M.op X1 (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq20952 X0 X1
       have i₂ := eq17823 (M.op X1 (M.op X1 (σ X0)))
       grind)
    | exact superpose eq17823 eq20952
    | exact resolve eq20952 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20952
  have eq21040 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op X1 (M.op X1 (σ X0))))) = (τ (M.op X1 (M.op (M.op X1 (σ X0)) (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq20997 X0 X1
       have i₂ := eq19 (M.op X1 (σ X0)) X1
       grind)
    | exact superpose eq19 eq20997
    | exact resolve eq20997 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20997
  have eq21066 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (M.op X0 X0) (τ (M.op X1 (M.op X1 (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq21040 X0 X1
       have i₂ := eq9 (σ X0) X1
       grind)
    | exact superpose eq9 eq21040
    | exact resolve eq21040 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21040
  have eq21088 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op X1 (M.op X1 (σ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq21066 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21066
    | exact resolve eq21066 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21066
  have eq23787 : ∀ X0 X1 X2 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18407 (M.op X1 (M.op X1 X0)) X2 (τ X0)
       have i₂ := eq19248 X0 X1
       grind)
    | exact superpose eq19248 eq18407
    | exact resolve eq18407 eq19248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18407 eq19248
  have eq26204 : ∀ X0 X1 X2 X3 : G, (τ (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2))))) = (τ (M.op (M.op X3 (M.op X3 X2)) (M.op (M.op X3 (M.op X3 X2)) (M.op X3 (M.op X3 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20891 (M.op X3 (M.op X3 X2)) X1
       have i₂ := eq239 X3 X2 X0 X1
       grind)
    | (have i₁ := eq20891 (M.op X2 (M.op X3 X1)) X2
       have i₂ := eq239 X0 X1 X2 X3
       grind)
    | exact superpose eq239 eq20891
    | exact resolve eq20891 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239 eq20891
  have eq26424 : ∀ X0 X1 X2 : G, (M.op (τ X2) (τ X2)) = (τ (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26204 X0 X1 X2 x
       have i₂ := eq23787 X2 x (M.op x (M.op x X2))
       grind)
    | exact superpose eq23787 eq26204
    | exact resolve eq26204 eq23787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23787 eq26204
  have eq54915 : x = (M.op y (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq3822
       grind)
    | exact superpose eq3822 eq9
    | exact resolve eq9 eq3822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54925 : x = (M.op x (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq155 y x
       have i₂ := eq3822
       grind)
    | exact superpose eq3822 eq155
    | exact resolve eq155 eq3822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq3822
  have eq55025 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x (M.op y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq54925
       have i₂ := eq17829 x
       grind)
    | exact superpose eq17829 eq54925
    | exact resolve eq54925 eq17829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54925
  have eq55035 : x = (M.op y (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq54915
       have i₂ := eq17829 x
       grind)
    | exact superpose eq17829 eq54915
    | exact resolve eq54915 eq17829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54915
  have eq196488 : ∀ X0 X1 X2 : G, (σ (τ X2)) ≠ (σ (τ (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))))) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17776 (τ X2)
       have i₂ := eq26424 X1 X0 X2
       grind)
    | exact superpose eq26424 eq17776
    | (have j0 := eq17776 (τ X2)
       grind)
    | exact resolve eq17776 eq26424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17776 eq26424
  have eq197131 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))) ≠ (σ (τ X2)) ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq196488 X0 X1 X2
       have i₂ := eq11 (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2))))
       grind)
    | exact superpose eq11 eq196488
    | (have j0 := eq196488 X0 X1 X2
       grind)
    | exact resolve eq196488 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196488
  have eq197828 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))) ≠ X2 ∨ (σ (τ X2)) = (M.op (σ (τ X2)) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq197131 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq197131
    | (have j0 := eq197131 X0 X1 X2
       grind)
    | exact resolve eq197131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197131
  have eq198293 : ∀ X0 X1 X2 : G, (σ (τ X2)) = (σ (M.op (τ X2) (τ X2))) ∨ (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))) ≠ X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq197828 X0 X1 X2
       have i₂ := eq17829 (τ X2)
       grind)
    | exact superpose eq17829 eq197828
    | (have j0 := eq197828 X0 X1 X2
       grind)
    | exact resolve eq197828 eq17829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197828
  have eq198596 : ∀ X0 X1 X2 : G, (σ (τ X2)) = (σ (τ (M.op X2 X2))) ∨ (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))) ≠ X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198293 X0 X1 X2
       have i₂ := eq17823 X2
       grind)
    | exact superpose eq17823 eq198293
    | (have j0 := eq198293 X0 X1 X2
       grind)
    | exact resolve eq198293 eq17823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17823 eq198293
  have eq198779 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (τ X2)) ∨ (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))) ≠ X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198596 X0 X1 X2
       have i₂ := eq11 (M.op X2 X2)
       grind)
    | exact superpose eq11 eq198596
    | (have j0 := eq198596 X0 X1 X2
       grind)
    | exact resolve eq198596 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198596
  have eq198874 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))) ≠ X2 ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198779 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq198779
    | (have j0 := eq198779 X0 X1 X2
       grind)
    | exact resolve eq198779 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198779
  have eq1962882 : x ≠ (M.op x (M.op y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq198874 x y x
       have i₂ := eq55035
       grind)
    | exact superpose eq55035 eq198874
    | (have j0 := eq198874 x x x
       grind)
    | exact resolve eq198874 eq55035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55035 eq198874
  have eq1963172 : x ≠ (M.op x (M.op y x)) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1962882
  have eq1963452 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1963172
       have r₂ := eq55025
       grind)
    | exact resolve eq1963172 eq55025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55025 eq1963172
  have eq2157973 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x ≠ (M.op X0 (M.op X0 (M.op X1 (M.op X1 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq107
       have i₂ := eq676 X0 X1 x y
       grind)
    | exact superpose eq676 eq107
    | (have j1 := eq676 X0 X1 x x
       grind)
    | exact resolve eq107 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq676
  have eq2157974 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x ≠ (M.op X0 (M.op X0 (M.op X1 (M.op X1 x)))) := by
    intro X0 X1
    first
    | (have j0 := eq2157973 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157973
  have eq2157975 : ∀ X0 X1 : G, (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x ≠ (M.op X0 (M.op X0 (M.op X1 (M.op X1 x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2157974 X0 X1
       have i₂ := eq17829 x
       grind)
    | exact superpose eq17829 eq2157974
    | (have j0 := eq2157974 X0 X1
       grind)
    | exact resolve eq2157974 eq17829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157974
  have eq2158258 : x ≠ (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2157975 x x
       have i₂ := eq158 x x x
       grind)
    | exact superpose eq158 eq2157975
    | exact resolve eq2157975 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq2157975
  have eq2158342 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2158258
       have r₂ := eq1963452
       grind)
    | exact resolve eq2158258 eq1963452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963452 eq2158258
  have eq2160168 : x = (M.op x (τ (M.op (σ y) (σ x)))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq20560 x (σ y)
       have i₂ := eq2158342
       grind)
    | exact superpose eq2158342 eq20560
    | exact resolve eq20560 eq2158342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2160261 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq2158342
       grind)
    | exact superpose eq2158342 eq9
    | exact resolve eq9 eq2158342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2158342
  have eq2160804 : (σ x) = (M.op (σ y) (σ (M.op x x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2160261
       have i₂ := eq17829 x
       grind)
    | exact superpose eq17829 eq2160261
    | exact resolve eq2160261 eq17829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17829 eq2160261
  have eq2163594 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x x))) = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq20983 (M.op x x) X0 (σ y)
       have i₂ := eq2160804
       grind)
    | exact superpose eq2160804 eq20983
    | exact resolve eq20983 eq2160804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20983 eq2160804
  have eq2164336 : x = (τ (M.op (σ y) (σ x))) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2163594 x
       have i₂ := eq69 x x
       grind)
    | exact superpose eq69 eq2163594
    | exact resolve eq2163594 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2163594
  have eq2175050 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2160168
       have i₂ := eq2164336
       grind)
    | exact superpose eq2164336 eq2160168
    | exact resolve eq2160168 eq2164336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160168 eq2164336
  have eq2175457 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq2175050
  have eq2178194 : ∀ X0 : G, (M.op x x) = (M.op (M.op x x) (τ (M.op X0 (M.op X0 (σ x))))) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq20560 (M.op x x) X0
       have i₂ := eq2175457
       grind)
    | exact superpose eq2175457 eq20560
    | exact resolve eq20560 eq2175457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20560 eq2175457
  have eq2178571 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2178194 x
       have i₂ := eq21088 x x
       grind)
    | exact superpose eq21088 eq2178194
    | exact resolve eq2178194 eq21088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21088 eq2178194
  have eq2178572 : x = (M.op x x) := by grind
  clear eq2178571
  have eq2178983 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq2178572
       grind)
    | exact superpose eq2178572 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq2178572
       grind)
    | exact resolve eq12 eq2178572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2179019 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq17777 x X0
       have i₂ := eq2178572
       grind)
    | exact superpose eq2178572 eq17777
    | (have j0 := eq17777 x X0
       grind)
    | exact resolve eq17777 eq2178572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17777 eq2178572
  have eq2179476 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2179019 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179019
  have eq2179481 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2178983 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178983
  have eq2193717 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq2179476 (σ X0)
       grind)
    | exact superpose eq2179476 eq15
    | exact resolve eq15 eq2179476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179476
  have eq2194018 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq2193717 X0
       have i₂ := eq2179481 X0
       grind)
    | exact superpose eq2179481 eq2193717
    | exact resolve eq2193717 eq2179481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179481 eq2193717
  have eq2210172 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2194018 y
       grind)
    | exact superpose eq2194018 eq16
    | (have r₁ := eq16
       have r₂ := eq2194018 y
       grind)
    | exact resolve eq16 eq2194018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194018
  have eq2211046 : False := by grind
  exact eq2211046

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq64 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq64
    | exact resolve eq64 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq10
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq98
    | exact resolve eq98 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq101 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq96
    | exact resolve eq96 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq102 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq95
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq103 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq24 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq24 eq94
    | exact resolve eq94 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq104 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq100
    | exact resolve eq100 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq105 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq101
    | exact resolve eq101 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq102
    | exact resolve eq102 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq103
    | exact resolve eq103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq129 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq139 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq129 y x
       grind)
    | exact superpose eq129 eq16
    | (have j1 := eq129 y x
       grind)
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq340 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1 (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq97
    | exact resolve eq97 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (M.op X2 (τ (M.op X0 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq340 (M.op X0 X1) X2
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq340
    | exact resolve eq340 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq363 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (k X0 (σ (τ X0))) (k X0 (σ (τ X0)))) := by
    intro X0
    grind
  clear eq62
  have eq388 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq363 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq363
    | exact resolve eq363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq395 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq388
  have eq397 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq395 X0
       have i₂ := eq24 (τ X0) (τ X0)
       grind)
    | exact superpose eq24 eq395
    | exact resolve eq395 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq398 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq397 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq397
    | exact resolve eq397 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq399 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq398 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq398
    | exact resolve eq398 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq657 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq139
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq139
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq139
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq139
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq139 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq658 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by grind
  clear eq657
  have eq686 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq66
    | exact resolve eq66 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq820 : ∀ X0 : G, (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq106 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq106
    | exact resolve eq106 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq820 X0
       have i₂ := eq97 (M.op (τ X0) (τ X0)) (τ X0)
       grind)
    | exact superpose eq97 eq820
    | exact resolve eq820 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq820
  have eq869 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq854 X0
       have i₂ := eq24 (τ X0) (τ X0)
       grind)
    | exact superpose eq24 eq854
    | exact resolve eq854 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq876 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (σ (M.op (τ X0) (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq869 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq869
    | exact resolve eq869 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq869
  have eq879 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq876 X0
       have i₂ := eq399 X0
       grind)
    | exact superpose eq399 eq876
    | exact resolve eq876 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq876
  have eq882 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq879 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq879
    | exact resolve eq879 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq884 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq882 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq882
    | exact resolve eq882 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq897 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq884 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq884
    | exact resolve eq884 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq884
  have eq1047 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 (σ X0)) (M.op X1 (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq107 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq107
    | exact resolve eq107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1334 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))))) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq105
    | exact resolve eq105 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1413 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))))) = (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1334 X0 X1
       have i₂ := eq24 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq24 eq1334
    | exact resolve eq1334 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1448 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))))) = (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1413 X0 X1
       have i₂ := eq24 (M.op X0 X0) X1
       grind)
    | exact superpose eq24 eq1413
    | exact resolve eq1413 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1473 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0)))))) = (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1448 X0 X1
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq1448
    | exact resolve eq1448 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1490 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1473 X1 X0
       have i₂ := eq104 X0 X1
       grind)
    | exact superpose eq104 eq1473
    | exact resolve eq1473 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1473
  have eq1504 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X1 X0))) = (M.op X1 (M.op (M.op X1 (M.op X0 (M.op X0 X0))) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1490 X0 X1
       have i₂ := eq105 X1 X0
       grind)
    | exact superpose eq105 eq1490
    | exact resolve eq1490 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq1490
  have eq3389 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq346 X1 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq346
    | exact resolve eq346 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq3596 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X2 (M.op X2 X1))
       have i₂ := eq3389 X1 X2 X0
       grind)
    | exact superpose eq3389 eq11
    | exact resolve eq11 eq3389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3636 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (M.op (τ X1) (τ X1))) (σ (τ (M.op X0 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq897 (τ X1)
       have i₂ := eq3389 X1 X0 (τ X1)
       grind)
    | exact superpose eq3389 eq897
    | exact resolve eq897 eq3389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq3389
  have eq3674 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (M.op (τ X1) (τ X1))) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3636 X0 X1
       have i₂ := eq11 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq11 eq3636
    | exact resolve eq3636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3636
  have eq3724 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3674 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq3674
    | exact resolve eq3674 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3674
  have eq3750 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3724 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3724
    | exact resolve eq3724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq9552 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq16
    | exact resolve eq16 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq9553 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9552
       have r₂ := eq22 x
       grind)
    | exact resolve eq9552 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9552
  have eq44285 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X2 (M.op X2 (τ X1))) (M.op X2 (M.op X2 (τ X1))))) = (M.op X3 (M.op (M.op X3 (M.op X0 (M.op X0 X1))) (M.op X3 (σ (M.op (M.op X2 (M.op X2 (τ X1))) (M.op X2 (M.op X2 (τ X1)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1047 (M.op X2 (M.op X2 (τ X1))) X3
       have i₂ := eq3596 X2 X1 X0
       grind)
    | exact superpose eq3596 eq1047
    | exact resolve eq1047 eq3596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq3596
  have eq44504 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 (M.op (M.op X2 (τ X1)) (M.op X2 (τ X1))))) = (M.op X3 (M.op (M.op X3 (M.op X0 (M.op X0 X1))) (M.op X3 (σ (M.op X2 (M.op (M.op X2 (τ X1)) (M.op X2 (τ X1)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44285 X0 X1 X1 X3
       have i₂ := eq24 (M.op X1 (τ X1)) X1
       grind)
    | exact superpose eq24 eq44285
    | exact resolve eq44285 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44285
  have eq44596 : ∀ X0 X1 X3 : G, (σ (τ X1)) = (M.op X3 (M.op (M.op X3 (M.op X0 (M.op X0 X1))) (M.op X3 (σ (τ X1))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq44504 X0 X1 X1 X3
       have i₂ := eq9 (τ X1) X1
       grind)
    | exact superpose eq9 eq44504
    | exact resolve eq44504 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44504
  have eq44668 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (M.op X3 (M.op X0 (M.op X0 X1))) (M.op X3 X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq44596 X0 X0 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq44596
    | exact resolve eq44596 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44596
  have eq85217 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 (M.op X0 (M.op X0 X0))) (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1504 X0 X1
       have i₂ := eq3750 X1 X0
       grind)
    | exact superpose eq3750 eq1504
    | exact resolve eq1504 eq3750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504 eq3750
  have eq346014 : (σ x) = (M.op (σ y) (M.op (σ (M.op y y)) (σ (M.op y y)))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq9553
       grind)
    | exact superpose eq9553 eq9
    | exact resolve eq9 eq9553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9553
  have eq346208 : (σ x) = (M.op (σ y) (σ (M.op (M.op y y) (M.op y y)))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq346014
       have i₂ := eq22 (M.op y y)
       grind)
    | exact superpose eq22 eq346014
    | exact resolve eq346014 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346014
  have eq346300 : (σ x) = (M.op (σ y) (σ (M.op y (M.op y y)))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq346208
       have i₂ := eq24 y y
       grind)
    | exact superpose eq24 eq346208
    | exact resolve eq346208 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq346208
  have eq346352 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq346300
       have i₂ := eq686 y
       grind)
    | exact superpose eq686 eq346300
    | exact resolve eq346300 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq346300
  have eq346353 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq346352
  have eq346615 : y = (M.op y (M.op (M.op y (M.op y (M.op y x))) (M.op y x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq85217 y y
       have i₂ := eq346353
       grind)
    | exact superpose eq346353 eq85217
    | exact resolve eq85217 eq346353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85217 eq346353
  have eq346647 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq346615
       have i₂ := eq44668 y x y
       grind)
    | exact superpose eq44668 eq346615
    | exact resolve eq346615 eq44668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44668 eq346615
  have eq347267 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq346647
       grind)
    | exact superpose eq346647 eq16
    | exact resolve eq16 eq346647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346647
  have eq347268 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq347267
       have r₂ := eq22 x
       grind)
    | exact resolve eq347267 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347267
  have eq347270 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq347268
       grind)
    | exact superpose eq347268 eq10
    | exact resolve eq10 eq347268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347268
  have eq347703 : x = y := by
    first
    | (have i₁ := eq347270
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq347270
    | exact resolve eq347270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347270
  have eq347715 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq347703
       grind)
    | exact superpose eq347703 eq16
    | exact resolve eq16 eq347703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347703
  have eq347716 : False := by grind
  exact eq347716

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq42 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq46 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq46
    | exact resolve eq46 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq47
    | exact resolve eq47 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq101 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq106 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq101
    | (have j0 := eq101 X0 X1
       grind)
    | exact resolve eq101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq135 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq42
    | exact resolve eq42 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq42 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq42
    | exact resolve eq42 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq42 X1 X0
       grind)
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq136 X0 X1
       have i₂ := eq42 (M.op X1 X1) X0
       grind)
    | exact superpose eq42 eq136
    | exact resolve eq136 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq146 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 X1
       have i₂ := eq42 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq42 eq135
    | exact resolve eq135 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq150 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq145 X0 X1
       have i₂ := eq42 X1 X1
       grind)
    | exact superpose eq42 eq145
    | exact resolve eq145 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq151 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq42 X0 X1
       grind)
    | exact superpose eq42 eq146
    | exact resolve eq146 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq152 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq150 X1 X0
       grind)
    | exact superpose eq150 eq151
    | exact resolve eq151 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq151
  have eq154 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq139
    | exact resolve eq139 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq222 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq206 X0 X1 X2
       have i₂ := eq44 X0 X1
       grind)
    | exact superpose eq44 eq206
    | (have j0 := eq206 X0 X1 X2
       grind)
    | exact resolve eq206 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq206
  have eq298 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq152 (M.op X0 X0) X1
       have i₂ := eq139 (M.op X0 X0) X0
       grind)
    | exact superpose eq139 eq152
    | exact resolve eq152 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq300 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq152 (σ (M.op X0 X0)) X1
       have i₂ := eq154 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq154 eq152
    | exact resolve eq152 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq154
  have eq314 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 X1
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq300
    | exact resolve eq300 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq316 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 X1
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq298
    | exact resolve eq298 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq321 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op X1 (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0 X1
       have i₂ := eq42 X0 X0
       grind)
    | exact superpose eq42 eq314
    | exact resolve eq314 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq326 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq316 X1 X2
       have i₂ := eq316 X1 X0
       grind)
    | (have i₁ := eq316 X0 X1
       have i₂ := eq316 X0 X0
       grind)
    | exact superpose eq316 eq316
    | exact resolve eq316 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X1
       have i₂ := eq316 X1 X0
       grind)
    | (have i₁ := eq48 X0
       have i₂ := eq316 X0 X0
       grind)
    | exact superpose eq316 eq48
    | exact resolve eq48 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq316
  have eq669 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ (M.op X0 (M.op X0 X1))) (σ X1)
       have i₂ := eq340 X0 X1
       grind)
    | exact superpose eq340 eq9
    | exact resolve eq9 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq678 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (σ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq321 X0 (σ X0)
       grind)
    | exact superpose eq321 eq669
    | exact resolve eq669 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq1875 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq321 X1 X2
       have i₂ := eq326 X1 X1 X0
       grind)
    | (have i₁ := eq321 X1 X2
       have i₂ := eq326 X0 X1 X1
       grind)
    | exact superpose eq326 eq321
    | exact resolve eq321 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq2763 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 X0)) (τ X2)) = (τ (k (σ (M.op X0 (M.op X0 X0))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq678 X0 X1
       grind)
    | (have i₁ := eq37 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq678 X0 X1
       grind)
    | exact superpose eq678 eq37
    | exact resolve eq37 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq2777 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 X0)) (τ X2)) = (k (M.op X0 (M.op X0 X0)) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2763 X0 X1 X2
       have i₂ := eq37 (M.op X0 (M.op X0 X0)) X2
       grind)
    | exact superpose eq37 eq2763
    | exact resolve eq2763 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2763
  have eq2938 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 (M.op X2 X1))
       have i₂ := eq1875 X2 X1 X0
       grind)
    | exact superpose eq1875 eq10
    | exact resolve eq10 eq1875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq13343 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (k X0 (σ X1)) (M.op (M.op (k X0 (σ X1)) (k X0 (σ X1))) (M.op (k X0 (σ X1)) (k X0 (σ X1))))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X2) (k X0 (σ X1))
       have i₂ := eq222 X0 X1 X2
       grind)
    | exact superpose eq222 eq9
    | (have j1 := eq222 X0 X1 X2
       grind)
    | exact resolve eq9 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq13392 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ X2) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13343 X0 X1 X2
       have i₂ := eq9 (k X0 (σ X1)) (k X0 (σ X1))
       grind)
    | exact superpose eq9 eq13343
    | (have j0 := eq13343 X0 X1 X2
       grind)
    | exact resolve eq13343 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13343
  have eq13393 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq13392 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13392
  have eq239482 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X1 X2)) X0) = (k (M.op X2 (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2777 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2777
    | exact resolve eq2777 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2777
  have eq240724 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) = (k (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    grind
  clear eq239482
  have eq240826 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X1 X1))) = (k (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq240724 X0 X1
       have i₂ := eq42 (M.op X1 X1) X1
       grind)
    | exact superpose eq42 eq240724
    | exact resolve eq240724 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq240724
  have eq241034 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) (M.op X1 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq240826 X0 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq240826
    | exact resolve eq240826 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240826
  have eq241407 : ∀ X0 X1 : G, (k (τ (M.op X0 (M.op X0 (σ X1)))) (M.op X1 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq241034 x X1
       have i₂ := eq2938 X0 X1 x
       grind)
    | exact superpose eq2938 eq241034
    | exact resolve eq241034 eq2938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2938
  have eq241594 : ∀ X0 X1 : G, (σ X0) = (k (M.op X1 (M.op X1 (σ X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq241034 X1 (σ X0)
       have i₂ := eq321 X0 (σ X0)
       grind)
    | exact superpose eq321 eq241034
    | exact resolve eq241034 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq241034
  have eq257907 : ∀ X0 X1 X2 : G, (σ (k X0 X2)) = (M.op (σ X2) (k (M.op X1 (M.op X1 (σ X0))) (σ (M.op X0 (M.op X0 X0))))) ∨ (σ X2) = (k (M.op X1 (M.op X1 (σ X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13393 (M.op X1 (M.op X1 (σ X0))) (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq241407 X1 X0
       grind)
    | exact superpose eq241407 eq13393
    | (have j0 := eq13393 (M.op X1 (M.op X1 (σ X0))) (M.op X0 (M.op X0 X0)) X2
       grind)
    | exact resolve eq13393 eq241407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13393 eq241407
  have eq257916 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (σ X2) = (k (M.op X1 (M.op X1 (σ X0))) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq257907 X0 X1 X2
       have i₂ := eq241594 X0 X1
       grind)
    | exact superpose eq241594 eq257907
    | (have j0 := eq257907 X0 X1 X2
       grind)
    | exact resolve eq257907 eq241594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257907
  have eq258159 : ∀ X0 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq257916 X0 x X2
       have i₂ := eq241594 X0 x
       grind)
    | exact superpose eq241594 eq257916
    | (have j0 := eq257916 X0 x X2
       grind)
    | exact resolve eq257916 eq241594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241594 eq257916
  have eq297236 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq258159 (τ X0) x
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq258159
    | exact resolve eq258159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297340 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq258159 y x
       grind)
    | exact superpose eq258159 eq16
    | (have j1 := eq258159 x y
       grind)
    | exact resolve eq16 eq258159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258159
  have eq297700 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq297236 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq297236
    | (have j0 := eq297236 X0 X1
       grind)
    | exact resolve eq297236 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq297236
  have eq298679 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq297700 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq297700
    | exact resolve eq297700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297700
  have eq300206 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq297340
       have i₂ := eq298679 x y
       grind)
    | exact superpose eq298679 eq297340
    | (have j1 := eq298679 (σ x) (σ y)
       grind)
    | (have r₁ := eq297340
       have r₂ := eq298679 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq297340
       have r₂ := eq298679 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq297340 eq298679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297340 eq298679
  have eq300211 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq300206
  have eq300398 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq300211
       grind)
    | exact superpose eq300211 eq16
    | exact resolve eq16 eq300211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300211
  have eq300399 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq300398
       have r₂ := eq22 x
       grind)
    | exact resolve eq300398 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300398
  have eq300400 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq300399
       grind)
    | exact superpose eq300399 eq16
    | exact resolve eq16 eq300399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300401 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq300399
       grind)
    | exact superpose eq300399 eq10
    | exact resolve eq10 eq300399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300399
  have eq300617 : x = y := by
    first
    | (have i₁ := eq300401
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq300401
    | exact resolve eq300401 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300401
  have eq300618 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq300400
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq300400
    | exact resolve eq300400 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq300400
  have eq300641 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq300618
       have i₂ := eq300617
       grind)
    | exact superpose eq300617 eq300618
    | exact resolve eq300618 eq300617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300617 eq300618
  have eq300642 : False := by grind
  exact eq300642
