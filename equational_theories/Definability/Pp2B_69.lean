import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4294`: `x ◇ (x ◇ y) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4294 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4294 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4294.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op X1 X2)) := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
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
  clear eq44
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq178 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X1 X2 X3
       grind)
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq178 X1
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) X1)) := by
    intro X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq197 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | (have i₁ := eq194 x X1
       have i₂ := eq186 x X1
       grind)
    | (have i₁ := eq194 x y
       have i₂ := eq186 x X1
       grind)
    | exact superpose eq186 eq194
    | exact resolve eq194 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq198 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq193 x
       have i₂ := eq186 sF2 x
       grind)
    | exact superpose eq186 eq193
    | (have j1 := eq186 (σ x) (σ y)
       grind)
    | exact resolve eq193 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq208 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq186 X0 (M.op X0 x)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq186
    | exact resolve eq186 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq186
  have eq219 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq198 eq208
    | exact resolve eq208 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq283 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq197 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq283 X0
       grind)
    | (have r₁ := eq283 X0
       have r₂ := eq198
       grind)
    | exact resolve eq283 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq283
  have eq406 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq219 (M.op sF2 sF4)
       have i₂ := eq291 (M.op sF2 sF4)
       grind)
    | exact superpose eq291 eq219
    | exact resolve eq219 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq512 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq539 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq455 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq455
    | exact resolve eq455 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq590 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | exact superpose eq291 eq512
    | exact resolve eq512 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1242 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq1246 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1257 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq291 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq291
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1288 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1257 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq2503 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1242
       grind)
    | exact superpose eq1242 eq40
    | exact resolve eq40 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq2504 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2503
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2503
    | exact resolve eq2503 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503
  have eq2506 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2504
    | exact resolve eq2504 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2504
  have eq18395 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq291 (M.op sF2 sF4)
       have i₂ := eq1288 (M.op sF2 sF4)
       grind)
    | exact superpose eq1288 eq291
    | (have j1 := eq1288 X0
       grind)
    | exact resolve eq291 eq1288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq18506 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18395 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq18395 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq18395 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18395
  have eq18627 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq192 X0 X0
       have i₂ := eq18506 X0
       grind)
    | exact superpose eq18506 eq192
    | exact resolve eq192 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18640 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq590 X0
       have i₂ := eq18506 (σ X0)
       grind)
    | exact superpose eq18506 eq590
    | exact resolve eq590 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq18657 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq18640 X0
       have i₂ := eq512 X0 (σ X0)
       grind)
    | exact superpose eq512 eq18640
    | exact resolve eq18640 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18640
  have eq18687 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq18657 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq18657
    | exact resolve eq18657 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18657
  have eq19059 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18627 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq18627
    | exact resolve eq18627 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19060 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq18627 (τ X0)
       have i₂ := eq539 X0 X0
       grind)
    | exact superpose eq539 eq18627
    | exact resolve eq18627 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22430 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq406 eq19059
    | exact resolve eq19059 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22528 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq22430
       have i₂ := eq291 (σ (M.op sF2 sF4))
       grind)
    | exact superpose eq291 eq22430
    | exact resolve eq22430 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq22430
  have eq25601 : (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq22528 eq512
    | exact resolve eq512 eq22528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq22528
  have eq25608 : (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq18687 eq25601
    | exact resolve eq25601 eq18687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18687 eq25601
  have eq25610 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq406 eq25608
    | exact resolve eq25608 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq25608
  have eq25624 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq25610 eq14
    | exact resolve eq14 eq25610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25610
  have eq33806 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2506 eq1246
    | exact resolve eq1246 eq2506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1246 eq2506
  have eq33813 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq33806
       have r₂ := eq27
       grind)
    | exact resolve eq33806 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33806
  have eq33819 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq33813
       have i₂ := eq18506 sF2
       grind)
    | exact superpose eq18506 eq33813
    | exact resolve eq33813 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33813
  have eq33823 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq33819
       have i₂ := eq18506 sF3
       grind)
    | exact superpose eq18506 eq33819
    | exact resolve eq33819 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33819
  have eq33827 : y = (k x x) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq33823
       have i₂ := eq18506 x
       grind)
    | exact superpose eq18506 eq33823
    | exact resolve eq33823 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33823
  have eq33829 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq33827
       have i₂ := eq18506 y
       grind)
    | exact superpose eq18506 eq33827
    | exact resolve eq33827 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33827
  have eq33836 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq33829 eq152
    | exact resolve eq152 eq33829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq33829
  have eq33864 : y = (k y y) ∨ y = (k x x) ∨ y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq31 eq33836
    | exact resolve eq33836 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33836
  have eq33865 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ y = (k y y) := by grind
  clear eq33864
  have eq33886 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq33865 eq97
    | exact resolve eq97 eq33865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq33865
  have eq33911 : y = (k x x) ∨ y = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq33886
    | exact resolve eq33886 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33886
  have eq33912 : y = (k y y) ∨ y = (k x x) := by grind
  clear eq33911
  have eq33927 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq33912
       grind)
    | exact superpose eq33912 eq40
    | exact resolve eq40 eq33912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33935 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq18627 y
       have i₂ := eq33912
       grind)
    | exact superpose eq33912 eq18627
    | exact resolve eq18627 eq33912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33936 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19059 y
       have i₂ := eq33912
       grind)
    | exact superpose eq33912 eq19059
    | exact resolve eq19059 eq33912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33937 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq19060 y
       have i₂ := eq33912
       grind)
    | exact superpose eq33912 eq19060
    | exact resolve eq19060 eq33912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19060
  have eq33946 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33937
       have i₂ := eq18506 (τ y)
       grind)
    | exact superpose eq18506 eq33937
    | exact resolve eq33937 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33937
  have eq33947 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33936
       have i₂ := eq18506 (σ y)
       grind)
    | exact superpose eq18506 eq33936
    | exact resolve eq33936 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33936
  have eq33948 : (k y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33935
       have i₂ := eq18506 y
       grind)
    | exact superpose eq18506 eq33935
    | exact resolve eq33935 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33935
  have eq33955 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33927
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33927
    | exact resolve eq33927 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33927
  have eq33961 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (k y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33946
       have i₂ := eq539 y y
       grind)
    | exact superpose eq539 eq33946
    | exact resolve eq33946 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq33946
  have eq33962 : (σ (k y y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33947
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq33947
    | exact resolve eq33947 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33947
  have eq33963 : y = (k x x) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq33912 eq33948
    | exact resolve eq33948 eq33912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33948
  have eq33970 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ y) ∨ y = (k x x) := by
    first
    | exact superpose eq33912 eq33961
    | exact resolve eq33961 eq33912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33912 eq33961
  have eq33971 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33962
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq33962
    | exact resolve eq33962 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq33962
  have eq33975 : y = (k x x) ∨ y = (τ y) := by
    first
    | exact superpose eq33963 eq33970
    | exact resolve eq33970 eq33963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33970
  have eq33976 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq33971
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33971
    | exact resolve eq33971 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33971
  have eq33980 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | exact superpose eq33955 eq33976
    | exact resolve eq33976 eq33955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33955 eq33976
  have eq33995 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq18627 x
       have i₂ := eq33975
       grind)
    | exact superpose eq33975 eq18627
    | exact resolve eq18627 eq33975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33996 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq19059 x
       have i₂ := eq33975
       grind)
    | exact superpose eq33975 eq19059
    | exact resolve eq19059 eq33975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33975
  have eq34001 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq33996
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33996
    | exact resolve eq33996 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33996
  have eq34002 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq33995
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33995
    | exact resolve eq33995 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33995
  have eq34013 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq34001
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34001
    | exact resolve eq34001 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34001
  have eq34020 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | exact superpose eq26 eq34013
    | exact resolve eq34013 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34013
  have eq34023 : y = (τ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34002 eq34020
    | exact resolve eq34020 eq34002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34020
  have eq34028 : y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq34023
       grind)
    | exact superpose eq34023 eq14
    | exact resolve eq14 eq34023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34023
  have eq34084 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq34028
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34028
    | exact resolve eq34028 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34028
  have eq34099 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq34084 eq27
    | exact resolve eq27 eq34084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34084
  have eq34617 : (M.op x y) = (σ (M.op x y)) ∨ y = (τ y) := by
    first
    | exact superpose eq34002 eq25624
    | exact resolve eq25624 eq34002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34002
  have eq34641 : y = (τ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq34617
    | exact resolve eq34617 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34617
  have eq34805 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq34641
       grind)
    | exact superpose eq34641 eq14
    | exact resolve eq14 eq34641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34641
  have eq34861 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq34805
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq34805
    | exact resolve eq34805 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34805
  have eq34868 : y = (σ y) := by
    first
    | (have r₁ := eq34861
       have r₂ := eq34099
       grind)
    | exact resolve eq34861 eq34099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34099 eq34861
  have eq34884 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq34868
       grind)
    | exact superpose eq34868 eq18
    | exact resolve eq18 eq34868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34885 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq34868
       grind)
    | exact superpose eq34868 eq24
    | exact resolve eq24 eq34868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38061 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq18627 x
       have i₂ := eq33963
       grind)
    | exact superpose eq33963 eq18627
    | exact resolve eq18627 eq33963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18627
  have eq38062 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19059 x
       have i₂ := eq33963
       grind)
    | exact superpose eq33963 eq19059
    | exact resolve eq19059 eq33963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19059 eq33963
  have eq38069 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38062
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38062
    | exact resolve eq38062 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38062
  have eq38070 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38061
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq38061
    | exact resolve eq38061 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq38061
  have eq38086 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38069
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38069
    | exact resolve eq38069 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq38069
  have eq38087 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38070
       have i₂ := eq34868
       grind)
    | exact superpose eq34868 eq38070
    | exact resolve eq38070 eq34868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38070
  have eq38103 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq38086
    | exact resolve eq38086 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38086
  have eq38116 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq38103
       have i₂ := eq34868
       grind)
    | exact superpose eq34868 eq38103
    | exact resolve eq38103 eq34868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38103
  have eq38125 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38087 eq38116
    | exact resolve eq38116 eq38087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38087 eq38116
  have eq38142 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq38125 eq219
    | exact resolve eq219 eq38125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38232 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38125 eq192
    | exact resolve eq192 eq38125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38125
  have eq38233 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq38232
    | exact resolve eq38232 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38232
  have eq38493 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq38233
  have eq38847 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38142 eq34884
    | exact resolve eq34884 eq38142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38142
  have eq38854 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq38847
       have r₂ := eq38493
       grind)
    | exact resolve eq38847 eq38493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38493 eq38847
  have eq38876 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq38854 eq27
    | exact resolve eq27 eq38854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq38878 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq38854 eq197
    | exact resolve eq197 eq38854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq38879 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq38854 eq219
    | exact resolve eq219 eq38854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq38952 : (M.op (σ x) (M.op x y)) = (σ (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq38854 eq25624
    | exact resolve eq25624 eq38854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25624
  have eq39013 : (M.op x (M.op x y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq38879 eq38878
    | exact resolve eq38878 eq38879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38878
  have eq39080 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op (σ x) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq39013 eq183
    | exact resolve eq183 eq39013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq39013
  have eq39086 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq38879 eq39080
    | exact resolve eq39080 eq38879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38879 eq39080
  have eq40158 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (σ x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq39086 X0 X0
       have i₂ := eq18506 X0
       grind)
    | exact superpose eq18506 eq39086
    | exact resolve eq39086 eq18506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18506 eq39086
  have eq40758 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq33980 eq192
    | exact resolve eq192 eq33980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq33980
  have eq40761 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq26 eq40758
    | exact resolve eq40758 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq40758
  have eq40847 : (M.op x y) = (σ y) ∨ y = (k x x) := by
    first
    | exact superpose eq38854 eq40761
    | exact resolve eq40761 eq38854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38854 eq40761
  have eq40906 : (σ y) = (k x x) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq40847
       have i₂ := eq34868
       grind)
    | exact superpose eq34868 eq40847
    | exact resolve eq40847 eq34868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34868 eq40847
  have eq41016 : (M.op (σ x) (M.op x y)) = (M.op x (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq40158 x
       have i₂ := eq40906
       grind)
    | exact superpose eq40906 eq40158
    | exact resolve eq40158 eq40906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40158 eq40906
  have eq41017 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq34884 eq41016
    | exact resolve eq41016 eq34884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34884 eq41016
  have eq41208 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq41017 eq38952
    | exact resolve eq38952 eq41017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38952 eq41017
  have eq41226 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq41208
    | exact resolve eq41208 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41208
  have eq41231 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq41226
       have r₂ := eq38876
       grind)
    | exact resolve eq41226 eq38876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41226
  have eq41293 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41231 eq34885
    | exact resolve eq34885 eq41231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34885 eq41231
  have eq42197 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41293 eq20
    | exact resolve eq20 eq41293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq41293
  have eq42353 : False := by grind
  exact eq42353

/-- `Equation4311`: `x ◇ (x ◇ y) = z ◇ (w ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation4311 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4311 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4311.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
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
  clear eq36
  have eq47 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq79
    | exact resolve eq79 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq216 : (M.op x (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq47 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47
    | (have j0 := eq47 y x
       grind)
    | exact resolve eq47 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op x X0) X2 X3
       have i₂ := eq47 X0 x
       grind)
    | exact superpose eq47 eq14
    | exact resolve eq14 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq227 X0 x x
       have i₂ := eq47 x x
       grind)
    | exact superpose eq47 eq227
    | exact resolve eq227 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq235 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq48 x x
       have i₂ := eq47 x x
       grind)
    | exact superpose eq47 eq48
    | exact resolve eq48 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq246 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq216 eq53
    | exact resolve eq53 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq216
  have eq811 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq71 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq71 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq71 X1 X1
       grind)
    | exact resolve eq12 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq821 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq811 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq827 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq821 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq821 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq821 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq821 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq837 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq827
    | (have j0 := eq827 X0 X1
       grind)
    | exact resolve eq827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq6411 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq837
  have eq6526 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6411 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6411
  have eq6527 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6526 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526
  have eq6969 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6527 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6527
    | (have j0 := eq6527 x
       grind)
    | exact resolve eq6527 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6980 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq47 (σ X0) (σ X0)
       have i₂ := eq6527 X0
       grind)
    | exact superpose eq6527 eq47
    | exact resolve eq47 eq6527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq6996 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq6969
       grind)
    | exact superpose eq6969 eq16
    | exact resolve eq16 eq6969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6969
  have eq7486 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq228 eq6980
    | exact resolve eq6980 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7521 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq7486
       have i₂ := eq6527 (M.op x sF0)
       grind)
    | exact superpose eq6527 eq7486
    | exact resolve eq7486 eq6527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6527 eq7486
  have eq7535 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq228 eq7521
    | exact resolve eq7521 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7521
  have eq7542 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq7535 eq16
    | exact resolve eq16 eq7535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq81 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq14403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14394
    | exact resolve eq14394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14394
  have eq14415 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq14403
       have r₂ := eq28
       grind)
    | exact resolve eq14403 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14403
  have eq14417 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq14415
    | exact resolve eq14415 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14415
  have eq14419 : (τ (σ y)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq14417 eq6996
    | exact resolve eq6996 eq14417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6996 eq14417
  have eq14443 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq14419
    | exact resolve eq14419 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14419
  have eq14444 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14443
  have eq14456 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6980 x
       have i₂ := eq14444
       grind)
    | exact superpose eq14444 eq6980
    | exact resolve eq6980 eq14444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6980
  have eq14462 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq246 x x
       have i₂ := eq14444
       grind)
    | exact superpose eq14444 eq246
    | exact resolve eq246 eq14444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq14444
  have eq14463 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14462
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14462
    | exact resolve eq14462 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14462
  have eq14467 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14456
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14456
    | exact resolve eq14456 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14456
  have eq14476 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14467
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14467
    | exact resolve eq14467 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq14467
  have eq14477 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14476
    | exact resolve eq14476 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14476
  have eq14713 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14463 eq7535
    | exact resolve eq7535 eq14463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14734 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq14713
    | exact resolve eq14713 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14713
  have eq14737 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14734 eq235
    | exact resolve eq235 eq14734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14740 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq14737
    | exact resolve eq14737 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14737
  have eq15144 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14477 eq14463
    | exact resolve eq14463 eq14477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14463 eq14477
  have eq15154 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15144
  have eq15323 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15154 eq235
    | exact resolve eq235 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq15325 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq15327 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq15323
    | exact resolve eq15323 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15323
  have eq16465 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14740 eq228
    | exact resolve eq228 eq14740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16475 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14740 eq7542
    | exact resolve eq7542 eq14740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14740
  have eq16724 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14734 eq16475
    | exact resolve eq16475 eq14734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16475
  have eq16757 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq16724
  have eq16759 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq16757
    | exact resolve eq16757 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16757
  have eq17100 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15327 eq228
    | exact resolve eq228 eq15327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17110 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15327 eq7542
    | exact resolve eq7542 eq15327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7542 eq15327
  have eq17365 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15154 eq17110
    | exact resolve eq17110 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17110
  have eq17400 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq17365
  have eq17402 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17400
       have r₂ := eq15325
       grind)
    | exact resolve eq17400 eq15325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17400
  have eq17403 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq17402
    | exact resolve eq17402 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17402
  have eq17406 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq17403 eq28
    | exact resolve eq28 eq17403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17403
  have eq17427 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq17406
       have r₂ := eq16759
       grind)
    | exact resolve eq17406 eq16759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16759 eq17406
  have eq17896 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14734 eq16465
    | exact resolve eq16465 eq14734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14734 eq16465
  have eq17916 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17896 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17896
  have eq17968 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15154 eq17100
    | exact resolve eq17100 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15154 eq17100
  have eq17990 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17968
  have eq17996 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17990 X0
       grind)
    | (have r₁ := eq17990 X0
       have r₂ := eq15325
       grind)
    | exact resolve eq17990 eq15325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15325 eq17990
  have eq18040 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17427 eq17916
    | exact resolve eq17916 eq17427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17916
  have eq18065 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq18040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18040
  have eq18146 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq17427 eq17996
    | exact resolve eq17996 eq17427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17427 eq17996
  have eq18171 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq18146 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18146
  have eq18857 : y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18065 x
       grind)
    | exact superpose eq18065 eq19
    | (have j1 := eq18065 x
       grind)
    | exact resolve eq19 eq18065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18065
  have eq18868 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq18857
  have eq20348 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq18171 x
       grind)
    | exact superpose eq18171 eq19
    | (have j1 := eq18171 x
       grind)
    | exact resolve eq19 eq18171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18171
  have eq20359 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq20348
  have eq20376 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20359 eq28
    | exact resolve eq28 eq20359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20359
  have eq20403 : y = (M.op x y) := by
    first
    | (have r₁ := eq20376
       have r₂ := eq18868
       grind)
    | exact resolve eq20376 eq18868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18868 eq20376
  have eq20404 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20403 eq21
    | exact resolve eq21 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20451 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20403 eq228
    | exact resolve eq228 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq20478 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20403 eq7535
    | exact resolve eq7535 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7535
  have eq20490 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq20478
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20478
    | exact resolve eq20478 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20478
  have eq20517 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq20451 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20451
    | (have j0 := eq20451 X0
       grind)
    | exact resolve eq20451 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20451
  have eq20563 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq20404
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20404
    | exact resolve eq20404 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20404
  have eq20569 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq20490
    | exact resolve eq20490 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq20490
  have eq20580 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq20403 eq20517
    | exact resolve eq20517 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20517
  have eq20586 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq20403 eq20569
    | exact resolve eq20569 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20403 eq20569
  have eq20596 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20563 eq27
    | exact resolve eq27 eq20563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20563
  have eq21394 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq20586 eq20596
    | exact resolve eq20596 eq20586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20596
  have eq21395 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq21394
       have i₂ := eq20580 sF2
       grind)
    | exact superpose eq20580 eq21394
    | exact resolve eq21394 eq20580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20580 eq21394
  have eq21400 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq21395 eq28
    | exact resolve eq28 eq21395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq21395
  have eq21433 : False := by grind
  exact eq21433

/-- `Equation4311`: `x ◇ (x ◇ y) = z ◇ (w ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_pxx_pxx_pxy_Equation4311 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4311 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4311.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
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
  have eq175 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X4 X5 : G, (M.op X4 (M.op X5 X4)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op x X2) X4 X5
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | (have i₁ := eq16 X0 (M.op X0 X1) X2 x
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | (have i₁ := eq16 X0 X1 X1 X1
       have i₂ := eq16 X1 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (M.op y (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq181 x x
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq181
    | exact resolve eq181 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq188 : ∀ X2 X4 X5 : G, (M.op X4 (M.op X5 X4)) = (M.op X2 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq178 x x X2 X4 X5
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq178
    | exact resolve eq178 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq182
  have eq189 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq175 x x
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq175
    | exact resolve eq175 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq190 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X2
    first
    | (have i₁ := eq188 X2 x x
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq188
    | exact resolve eq188 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq191 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq187 eq16
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq195 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq190 eq192
    | exact resolve eq192 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq197 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq189 eq16
    | exact resolve eq16 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq198 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq197 x x
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq197
    | exact resolve eq197 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq201 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq176 (M.op X0 X1) X1
       have i₂ := eq176 X1 X0
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y) (σ x)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op x X0) X2 X3
       have i₂ := eq176 X0 x
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq212 X0 x x
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq212
    | exact resolve eq212 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq212
  have eq278 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq190 eq191
    | exact resolve eq191 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq191
  have eq282 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq206 eq278
    | exact resolve eq278 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq479 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq536 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq563 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq479 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq479
    | exact resolve eq479 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq1050 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq201 eq28
    | (have j0 := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq201 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq201
  have eq1051 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq1050 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1103 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq1109 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq1190 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq1051 X0
       grind)
    | exact superpose eq1051 eq11
    | exact resolve eq11 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X0 X1 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) ≠ X1 ∨ (k X0 X1) = (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1051 X0
       grind)
    | exact superpose eq1051 eq13
    | (have r₁ := eq13 X0 (k X0 (M.op (σ x) (M.op (σ x) (σ y))))
       have r₂ := eq1051 X0
       grind)
    | exact resolve eq13 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) ∨ (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | (have j0 := eq1190 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1225 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ x) (σ y)))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1215 X0
       have j1 := eq1205 X0 X0
       grind)
    | (have r₁ := eq1215 X0
       have r₂ := eq1205 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1215 (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq1205 (M.op (σ x) (M.op (σ x) (σ y))) (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y))))
       grind)
    | (have r₁ := eq1215 x
       have r₂ := eq1205 x x
       grind)
    | exact resolve eq1215 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq1215
  have eq1231 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1051 (M.op sF2 sF4)
       have i₂ := eq1225 (M.op sF2 sF4)
       grind)
    | exact superpose eq1225 eq1051
    | exact resolve eq1051 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1243 : ∀ X0 : G, (τ (k (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq536 X0 (σ X0)
       have i₂ := eq1225 (σ X0)
       grind)
    | (have i₁ := eq536 X0 (M.op (σ x) (M.op (σ x) (σ y)))
       have i₂ := eq1225 (σ X0)
       grind)
    | exact superpose eq1225 eq536
    | exact resolve eq536 eq1225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1225
  have eq1247 : ∀ X0 : G, (k X0 X0) = (τ (k (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1243 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1243
    | exact resolve eq1243 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1260 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1247 X0
       have i₂ := eq536 X0 (M.op sF2 sF4)
       grind)
    | exact superpose eq536 eq1247
    | exact resolve eq1247 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1299 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq195 X0 X0
       have i₂ := eq1231 X0
       grind)
    | exact superpose eq1231 eq195
    | exact resolve eq195 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1323 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1299 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1299
    | exact resolve eq1299 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1299 (τ X0)
       have i₂ := eq563 X0 X0
       grind)
    | exact superpose eq563 eq1299
    | exact resolve eq1299 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2737 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq282 eq1323
    | exact resolve eq1323 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2785 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ (M.op (σ x) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq2737
       have i₂ := eq1051 (σ (M.op sF2 sF4))
       grind)
    | exact superpose eq1051 eq2737
    | exact resolve eq2737 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq2737
  have eq3735 : (τ (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq2785 eq536
    | exact resolve eq536 eq2785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536 eq2785
  have eq3739 : (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1260 eq3735
    | exact resolve eq3735 eq1260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq3735
  have eq3742 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq282 eq3739
    | exact resolve eq3739 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq3739
  have eq3758 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3742 eq14
    | exact resolve eq14 eq3742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3742
  have eq5477 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1103
       grind)
    | exact superpose eq1103 eq41
    | exact resolve eq41 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq5478 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5477
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5477
    | exact resolve eq5477 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5477
  have eq5480 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq5478
    | exact resolve eq5478 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5478
  have eq5482 : y = (k y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5480
       have i₂ := eq1231 y
       grind)
    | exact superpose eq1231 eq5480
    | exact resolve eq5480 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5480
  have eq5484 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq5482
       have i₂ := eq1231 x
       grind)
    | exact superpose eq1231 eq5482
    | exact resolve eq5482 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5482
  have eq34932 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq5484 eq1109
    | exact resolve eq1109 eq5484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109 eq5484
  have eq34939 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq34932
       have r₂ := eq27
       grind)
    | exact resolve eq34932 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34932
  have eq34945 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq34939
       have i₂ := eq1231 sF3
       grind)
    | exact superpose eq1231 eq34939
    | exact resolve eq34939 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34939
  have eq34947 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq34945
       have i₂ := eq1231 sF2
       grind)
    | exact superpose eq1231 eq34945
    | exact resolve eq34945 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34945
  have eq34954 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq34947 eq153
    | exact resolve eq153 eq34947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq34947
  have eq34981 : y = (k y y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq34954
    | exact resolve eq34954 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34954
  have eq34982 : (σ y) = (k (σ x) (σ x)) ∨ y = (k y y) ∨ y = (k x x) := by grind
  clear eq34981
  have eq34999 : (τ (σ y)) = (k x x) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq34982 eq98
    | exact resolve eq98 eq34982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq34982
  have eq35022 : y = (k x x) ∨ y = (k y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq34999
    | exact resolve eq34999 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34999
  have eq35023 : y = (k y y) ∨ y = (k x x) := by grind
  clear eq35022
  have eq35035 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq35023
       grind)
    | exact superpose eq35023 eq41
    | exact resolve eq41 eq35023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35040 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1299 y
       have i₂ := eq35023
       grind)
    | exact superpose eq35023 eq1299
    | exact resolve eq1299 eq35023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35043 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1323 y
       have i₂ := eq35023
       grind)
    | exact superpose eq35023 eq1323
    | exact resolve eq1323 eq35023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35044 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq1324 y
       have i₂ := eq35023
       grind)
    | exact superpose eq35023 eq1324
    | exact resolve eq1324 eq35023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq35056 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (τ y) (τ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq35044
       have i₂ := eq1231 (τ y)
       grind)
    | exact superpose eq1231 eq35044
    | exact resolve eq35044 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35044
  have eq35057 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq35043
       have i₂ := eq1231 (σ y)
       grind)
    | exact superpose eq1231 eq35043
    | exact resolve eq35043 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35043
  have eq35058 : (k y y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq35040
       have i₂ := eq1231 y
       grind)
    | exact superpose eq1231 eq35040
    | exact resolve eq35040 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35040
  have eq35061 : (σ y) = (k (σ y) (σ y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq35035
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35035
    | exact resolve eq35035 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35035
  have eq35067 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (k y y)) ∨ y = (k x x) := by
    first
    | (have i₁ := eq35056
       have i₂ := eq563 y y
       grind)
    | exact superpose eq563 eq35056
    | exact resolve eq35056 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563 eq35056
  have eq35068 : (σ (k y y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq35057
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq35057
    | exact resolve eq35057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35057
  have eq35069 : y = (k x x) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq35023 eq35058
    | exact resolve eq35058 eq35023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35058
  have eq35072 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ y) ∨ y = (k x x) := by
    first
    | exact superpose eq35023 eq35067
    | exact resolve eq35067 eq35023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35023 eq35067
  have eq35073 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq35068
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq35068
    | exact resolve eq35068 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq35068
  have eq35076 : y = (k x x) ∨ y = (τ y) := by
    first
    | exact superpose eq35069 eq35072
    | exact resolve eq35072 eq35069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35072
  have eq35077 : (k (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | (have i₁ := eq35073
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35073
    | exact resolve eq35073 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35073
  have eq35080 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x x) := by
    first
    | exact superpose eq35061 eq35077
    | exact resolve eq35077 eq35061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35061 eq35077
  have eq35092 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq1299 x
       have i₂ := eq35076
       grind)
    | exact superpose eq35076 eq1299
    | exact resolve eq1299 eq35076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35095 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq1323 x
       have i₂ := eq35076
       grind)
    | exact superpose eq35076 eq1323
    | exact resolve eq1323 eq35076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35076
  have eq35103 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (τ y) := by
    first
    | (have i₁ := eq35095
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35095
    | exact resolve eq35095 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35095
  have eq35104 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq35092
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq35092
    | exact resolve eq35092 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35092
  have eq35113 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | (have i₁ := eq35103
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35103
    | exact resolve eq35103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35103
  have eq35118 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (τ y) := by
    first
    | exact superpose eq26 eq35113
    | exact resolve eq35113 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35113
  have eq35119 : y = (τ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35104 eq35118
    | exact resolve eq35118 eq35104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35118
  have eq35120 : y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq35119
       grind)
    | exact superpose eq35119 eq14
    | exact resolve eq14 eq35119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35119
  have eq35176 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq35120
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35120
    | exact resolve eq35120 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35120
  have eq35188 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq35176 eq27
    | exact resolve eq27 eq35176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35176
  have eq35758 : (M.op x y) = (σ (M.op x y)) ∨ y = (τ y) := by
    first
    | exact superpose eq35104 eq3758
    | exact resolve eq3758 eq35104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35104
  have eq35800 : y = (τ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq35758
    | exact resolve eq35758 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35758
  have eq36052 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq14 y
       have i₂ := eq35800
       grind)
    | exact superpose eq35800 eq14
    | exact resolve eq14 eq35800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35800
  have eq36108 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq36052
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq36052
    | exact resolve eq36052 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36052
  have eq36114 : y = (σ y) := by
    first
    | (have r₁ := eq36108
       have r₂ := eq35188
       grind)
    | exact resolve eq36108 eq35188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35188 eq36108
  have eq36123 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq36114
       grind)
    | exact superpose eq36114 eq18
    | exact resolve eq18 eq36114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36124 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq36114
       grind)
    | exact superpose eq36114 eq24
    | exact resolve eq24 eq36114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40267 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1299 x
       have i₂ := eq35069
       grind)
    | exact superpose eq35069 eq1299
    | exact resolve eq1299 eq35069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299
  have eq40270 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1323 x
       have i₂ := eq35069
       grind)
    | exact superpose eq35069 eq1323
    | exact resolve eq1323 eq35069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323 eq35069
  have eq40284 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40270
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40270
    | exact resolve eq40270 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq40270
  have eq40287 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40267
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40267
    | exact resolve eq40267 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq40267
  have eq40302 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40284
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40284
    | exact resolve eq40284 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq40284
  have eq40305 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40287
       have i₂ := eq36114
       grind)
    | exact superpose eq36114 eq40287
    | exact resolve eq40287 eq36114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40287
  have eq40319 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq40302
    | exact resolve eq40302 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40302
  have eq40331 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq40319
       have i₂ := eq36114
       grind)
    | exact superpose eq36114 eq40319
    | exact resolve eq40319 eq36114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40319
  have eq40337 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40305 eq40331
    | exact resolve eq40331 eq40305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40305 eq40331
  have eq40348 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq40337 eq213
    | exact resolve eq213 eq40337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40454 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40337 eq195
    | exact resolve eq195 eq40337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq40337
  have eq40457 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq40454
    | exact resolve eq40454 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq40454
  have eq40804 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq40457
  have eq41254 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40348 eq36123
    | exact resolve eq36123 eq40348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40348
  have eq41259 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq41254
       have r₂ := eq40804
       grind)
    | exact resolve eq41254 eq40804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40804 eq41254
  have eq41281 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq41259 eq27
    | exact resolve eq27 eq41259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq41287 : (M.op (σ x) (M.op x y)) = (M.op (σ y) (M.op x y)) := by
    first
    | exact superpose eq41259 eq206
    | exact resolve eq206 eq41259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq41288 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (M.op X0 (M.op (σ x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq41259 eq213
    | exact resolve eq213 eq41259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq41368 : (M.op (σ x) (M.op x y)) = (σ (M.op (σ x) (M.op x y))) := by
    first
    | exact superpose eq41259 eq3758
    | exact resolve eq3758 eq41259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3758 eq41259
  have eq41543 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (M.op (σ x) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq41287 eq186
    | exact resolve eq186 eq41287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq41287
  have eq41547 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq41288 eq41543
    | exact resolve eq41543 eq41288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41288 eq41543
  have eq43916 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (σ x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq41547 X0 X0
       have i₂ := eq1231 X0
       grind)
    | exact superpose eq1231 eq41547
    | exact resolve eq41547 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq41547
  have eq44650 : (σ y) = (M.op x (σ y)) ∨ y = (k x x) := by
    first
    | exact superpose eq35080 eq198
    | exact resolve eq198 eq35080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq35080
  have eq44865 : (M.op x y) = (σ y) ∨ y = (k x x) := by
    first
    | exact superpose eq36123 eq44650
    | exact resolve eq44650 eq36123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44650
  have eq44938 : (σ y) = (k x x) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq44865
       have i₂ := eq36114
       grind)
    | exact superpose eq36114 eq44865
    | exact resolve eq44865 eq36114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36114 eq44865
  have eq45109 : (M.op (σ x) (M.op x y)) = (M.op x (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq43916 x
       have i₂ := eq44938
       grind)
    | exact superpose eq44938 eq43916
    | exact resolve eq43916 eq44938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43916 eq44938
  have eq45116 : (M.op x y) = (M.op (σ x) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq36123 eq45109
    | exact resolve eq45109 eq36123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36123 eq45109
  have eq45291 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq45116 eq41368
    | exact resolve eq41368 eq45116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41368 eq45116
  have eq45322 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq45291
    | exact resolve eq45291 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45291
  have eq45332 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq45322
       have r₂ := eq41281
       grind)
    | exact resolve eq45322 eq41281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45322
  have eq45405 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq45332 eq36124
    | exact resolve eq36124 eq45332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36124 eq45332
  have eq45673 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq45405 eq20
    | exact resolve eq20 eq45405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq45405
  have eq45829 : False := by grind
  exact eq45829

/-- `Equation4311`: `x ◇ (x ◇ y) = z ◇ (w ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_y_pxx_pxy_Equation4311 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4311 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4311.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X3 X2)) := by
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
  clear eq44
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X4 X5 : G, (M.op X4 (M.op X5 X4)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq16 X2 x X0 X1
       grind)
    | (have i₁ := eq16 X2 (M.op x X2) X2 x
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X4 X5 : G, (M.op X4 (M.op X5 X4)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op x X2) X4 X5
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | (have i₁ := eq16 X0 (M.op X0 X1) X2 x
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X4 X5 : G, (M.op X0 (M.op X1 X0)) = (M.op X4 (M.op X5 X4)) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | (have i₁ := eq16 x x x x
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op y (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (M.op y (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq181 x x
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq181
    | exact resolve eq181 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq188 : ∀ X2 X4 X5 : G, (M.op X4 (M.op X5 X4)) = (M.op X2 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq178 x x X2 X4 X5
       have i₂ := eq182 x x
       grind)
    | exact superpose eq182 eq178
    | exact resolve eq178 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq189 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq175 x x
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq175
    | exact resolve eq175 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq190 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X2
    first
    | (have i₁ := eq188 X2 x x
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq188
    | exact resolve eq188 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq191 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq187 eq16
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq194 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq190 eq191
    | exact resolve eq191 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq208 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y) (σ x)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op x X0) X2 X3
       have i₂ := eq176 X0 x
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq214 X0 x x
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq214
    | exact resolve eq214 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq271 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq190 eq174
    | exact resolve eq174 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq281 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq208 eq271
    | exact resolve eq271 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq351 : (τ (M.op (σ x) (σ x))) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq362 : (τ (M.op (σ y) (σ y))) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq174
  have eq1059 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq1066 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq1074 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1075 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1074 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1137 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1075 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1075
    | (have j0 := eq1075 (σ X0)
       grind)
    | exact resolve eq1075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6189 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1059
       grind)
    | exact superpose eq1059 eq40
    | exact resolve eq40 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq6190 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq6189
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6189
    | exact resolve eq6189 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6189
  have eq6193 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq6190
    | exact resolve eq6190 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6190
  have eq16650 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) ≠ (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq281 eq1137
    | (have j0 := eq1137 (M.op (σ x) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq1137 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq16686 : (σ (M.op (σ x) (M.op (σ x) (σ y)))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by grind
  clear eq16650
  have eq16809 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq16686 eq179
    | exact resolve eq179 eq16686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq16819 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op (σ x) (M.op (σ x) (σ y)))) (σ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq16686 eq194
    | exact resolve eq194 eq16686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16832 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq16686 eq16809
    | exact resolve eq16809 eq16686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16809
  have eq16848 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq16832 x x
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq16832
    | exact resolve eq16832 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16832
  have eq17927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq6193 eq1066
    | exact resolve eq1066 eq6193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6193
  have eq17934 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17927
       have r₂ := eq27
       grind)
    | exact resolve eq17927 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17927
  have eq17941 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17934 eq362
    | exact resolve eq362 eq17934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq17934
  have eq17976 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17941
    | exact resolve eq17941 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17941
  have eq17989 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq17976
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq17976
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq17976
       have r₂ := eq13 x y
       grind)
    | exact resolve eq17976 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17976
  have eq17999 : (τ (σ y)) = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17989 eq351
    | exact resolve eq351 eq17989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq17989
  have eq18035 : y = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17999
    | exact resolve eq17999 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq17999
  have eq18047 : y = (k y y) ∨ y = (k x y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq18035
       have r₂ := eq13 x y
       grind)
    | exact resolve eq18035 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18035
  have eq18061 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1137 y
       have i₂ := eq18047
       grind)
    | exact superpose eq18047 eq1137
    | (have j0 := eq1137 y
       grind)
    | exact resolve eq1137 eq18047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq18065 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq1075 y
       have i₂ := eq18047
       grind)
    | exact superpose eq18047 eq1075
    | (have j0 := eq1075 y
       grind)
    | (have r₁ := eq1075 y
       have r₂ := eq18047
       grind)
    | exact resolve eq1075 eq18047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075 eq18047
  have eq18066 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq18065
  have eq18068 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by grind
  clear eq18061
  have eq18069 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq18068
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18068
    | exact resolve eq18068 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18068
  have eq18076 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1059
       have i₂ := eq18066
       grind)
    | exact superpose eq18066 eq1059
    | exact resolve eq1059 eq18066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059 eq18066
  have eq18080 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq18076
  have eq18105 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq18069 eq194
    | exact resolve eq194 eq18069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18109 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq18069 eq18105
    | exact resolve eq18105 eq18069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18069 eq18105
  have eq18205 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq18109 eq182
    | exact resolve eq182 eq18109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18220 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq208 eq18205
    | exact resolve eq18205 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18205
  have eq18237 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (k x y) := by
    first
    | exact superpose eq26 eq18220
    | exact resolve eq18220 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18220
  have eq18249 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18109 eq18237
    | exact resolve eq18237 eq18109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18109 eq18237
  have eq18454 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq18249
       grind)
    | exact superpose eq18249 eq35
    | exact resolve eq35 eq18249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq18249
  have eq18459 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18454
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18454
    | exact resolve eq18454 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18454
  have eq18484 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18459 eq1066
    | exact resolve eq1066 eq18459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq18459
  have eq18489 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq18484
  have eq18608 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 y y X2 X0 X1
       have i₂ := eq18080
       grind)
    | exact superpose eq18080 eq177
    | exact resolve eq177 eq18080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq18618 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq194 y y
       have i₂ := eq18080
       grind)
    | exact superpose eq18080 eq194
    | exact resolve eq194 eq18080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18622 : y = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18080 eq18618
    | exact resolve eq18618 eq18080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18618
  have eq18632 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X2
    first
    | (have i₁ := eq18608 x x X2
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq18608
    | exact resolve eq18608 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq18608
  have eq18647 : ∀ X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X2 y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X2
    first
    | exact superpose eq18080 eq18632
    | exact resolve eq18632 eq18080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18080 eq18632
  have eq18654 : ∀ X2 : G, y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op X2 y) := by
    intro X2
    first
    | exact superpose eq18622 eq18647
    | exact resolve eq18647 eq18622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18647
  have eq18831 : y = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18622 eq16848
    | exact resolve eq16848 eq18622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18622
  have eq18868 : y = (M.op x x) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq18831
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18831
    | exact resolve eq18831 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18831
  have eq18919 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq194 x x
       have i₂ := eq18868
       grind)
    | exact superpose eq18868 eq194
    | exact resolve eq194 eq18868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18868
  have eq18923 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq18919
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18919
    | exact resolve eq18919 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18919
  have eq18973 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq18923 eq16848
    | exact resolve eq16848 eq18923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19013 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq18973
    | exact resolve eq18973 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18973
  have eq19439 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq194 x x
       have i₂ := eq18654 X0
       grind)
    | exact superpose eq18654 eq194
    | (have j1 := eq18654 x
       grind)
    | exact resolve eq194 eq18654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18654
  have eq19443 : ∀ X0 : G, (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq19439 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19439
    | (have j0 := eq19439 x
       grind)
    | exact resolve eq19439 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19439
  have eq19463 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq18923 eq19443
    | (have j0 := eq19443 x
       grind)
    | exact resolve eq19443 eq18923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19443
  have eq20586 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19463 eq26
    | (have j1 := eq19463 (σ x)
       grind)
    | exact resolve eq26 eq19463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20666 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20586 eq16848
    | exact resolve eq16848 eq20586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16848
  have eq20710 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq20666
    | exact resolve eq20666 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20666
  have eq20750 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20710 eq215
    | exact resolve eq215 eq20710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq20786 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq26 eq20750
    | (have j0 := eq20750 X0
       grind)
    | exact resolve eq20750 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20750
  have eq20807 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20710 eq20786
    | exact resolve eq20786 eq20710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20710 eq20786
  have eq21571 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18489 eq194
    | exact resolve eq194 eq18489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21575 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18489 eq21571
    | exact resolve eq21571 eq18489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18489 eq21571
  have eq23184 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21575 eq182
    | exact resolve eq182 eq21575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq23204 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq208 eq23184
    | exact resolve eq23184 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq23184
  have eq23223 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq23204
    | exact resolve eq23204 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23204
  have eq23237 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21575 eq23223
    | exact resolve eq23223 eq21575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21575 eq23223
  have eq23238 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23237
  have eq23268 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23238 eq194
    | exact resolve eq194 eq23238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23238
  have eq23272 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23268
    | exact resolve eq23268 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23268
  have eq23338 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23272 eq20586
    | exact resolve eq20586 eq23272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20586 eq23272
  have eq23361 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq23338
  have eq23842 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23361 eq18923
    | exact resolve eq18923 eq23361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18923
  have eq23845 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq23842
  have eq23848 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23845
    | exact resolve eq23845 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23845
  have eq23849 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by grind
  clear eq23848
  have eq24019 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq23849 eq27
    | exact resolve eq27 eq23849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23849
  have eq24087 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq24019
       have r₂ := eq19013
       grind)
    | exact resolve eq24019 eq19013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19013 eq24019
  have eq24101 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24087
       grind)
    | exact superpose eq24087 eq18
    | exact resolve eq18 eq24087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24134 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq24087
  have eq24785 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24101 eq20807
    | exact resolve eq20807 eq24101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20807
  have eq24786 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq24101 eq19463
    | exact resolve eq19463 eq24101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19463 eq24101
  have eq24805 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq24786
  have eq24806 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq24785
  have eq24825 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq24805
       have r₂ := eq24134
       grind)
    | exact resolve eq24805 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24805
  have eq24826 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq24806
       have r₂ := eq24134
       grind)
    | exact resolve eq24806 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24134 eq24806
  have eq25017 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23361 eq24825
    | exact resolve eq24825 eq23361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23361 eq24825
  have eq25074 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq25017
  have eq25108 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq25074
    | exact resolve eq25074 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25074
  have eq25109 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq25108
  have eq25148 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq25109 eq27
    | exact resolve eq27 eq25109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25109
  have eq25219 : y = (M.op x y) := by
    first
    | (have r₁ := eq25148
       have r₂ := eq24826
       grind)
    | exact resolve eq25148 eq24826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24826 eq25148
  have eq25235 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq25219
       grind)
    | exact superpose eq25219 eq18
    | exact resolve eq18 eq25219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq25236 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq25219
       grind)
    | exact superpose eq25219 eq24
    | exact resolve eq24 eq25219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq25219
  have eq25277 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25236 eq20
    | exact resolve eq20 eq25236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25236
  have eq25705 : (M.op x y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq25235 eq189
    | exact resolve eq189 eq25235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq25235
  have eq25764 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq25705 eq16686
    | exact resolve eq16686 eq25705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16686
  have eq25766 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq25705 eq16819
    | exact resolve eq16819 eq25705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16819
  have eq25793 : (M.op x y) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq25705 eq194
    | exact resolve eq194 eq25705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq25705
  have eq25813 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq25766
    | exact resolve eq25766 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25766
  have eq25815 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq25764
    | exact resolve eq25764 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq25764
  have eq25828 : (M.op x y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq25277 eq25813
    | exact resolve eq25813 eq25277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25813
  have eq25830 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq25277 eq25815
    | exact resolve eq25815 eq25277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25815
  have eq25836 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq25828 eq25830
    | exact resolve eq25830 eq25828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25828 eq25830
  have eq25844 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq25836 eq26
    | exact resolve eq26 eq25836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq25996 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25793 eq25844
    | exact resolve eq25844 eq25793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25793 eq25844
  have eq26083 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq25996 eq27
    | exact resolve eq27 eq25996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25996
  have eq26142 : (M.op x y) ≠ (σ y) := by
    first
    | exact superpose eq25277 eq26083
    | exact resolve eq26083 eq25277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25277 eq26083
  have eq26150 : False := by grind
  exact eq26150

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_x_pxx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq60 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq14 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq73
    | exact resolve eq73 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq75
    | exact resolve eq75 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq76
    | exact resolve eq76 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq60 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq125 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq16
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq346 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq95 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq95
    | (have j0 := eq95 (σ X0)
       grind)
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq346 X0 (M.op X1 X1)
       have i₂ := eq86 X1 (σ X0)
       grind)
    | exact superpose eq86 eq346
    | exact resolve eq346 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq572 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq547 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq547
    | exact resolve eq547 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq631 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq69 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq649 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq631 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq650 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq649 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq652 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq650
    | (have j0 := eq650 X0 X1
       grind)
    | exact resolve eq650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq3667 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq6971 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq652 X0 X1
       have j1 := eq647 X0 X1
       grind)
    | (have r₁ := eq652 X0 X1
       have r₂ := eq647 X0 X1
       grind)
    | (have r₁ := eq652 X0 X0
       have r₂ := eq647 X0 X0
       grind)
    | exact resolve eq652 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq652
  have eq7066 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6971 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6971
    | exact resolve eq6971 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7146 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6971 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6971
    | (have j0 := eq6971 X0 y
       grind)
    | exact resolve eq6971 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6971
  have eq7193 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7066 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq7066
    | (have j0 := eq7066 X0 X1
       grind)
    | exact resolve eq7066 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq7066
  have eq19563 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7146 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7146
    | (have j0 := eq7146 x
       grind)
    | exact resolve eq7146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7146
  have eq19570 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19563
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq19563
    | exact resolve eq19563 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19563
  have eq19588 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq19570
    | exact resolve eq19570 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19570
  have eq19913 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7193 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq7193
    | (have j0 := eq7193 X1 X1
       grind)
    | exact resolve eq7193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7193
  have eq21136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq77 eq19588
    | exact resolve eq19588 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq21143 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq21136
       have r₂ := eq27
       grind)
    | exact resolve eq21136 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21136
  have eq21178 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq21143 eq572
    | exact resolve eq572 eq21143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq21143
  have eq21214 : ∀ X0 : G, (k X0 y) = X0 ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq21178
    | exact resolve eq21178 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21178
  have eq21218 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq21214 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq21214 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq21214 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21214
  have eq21220 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq91
       have i₂ := eq21218 X0
       grind)
    | (have i₁ := eq91
       have i₂ := eq21218 (M.op x x)
       grind)
    | exact superpose eq21218 eq91
    | (have j1 := eq21218 X0
       grind)
    | (have r₁ := eq91
       have r₂ := eq21218 X0
       grind)
    | exact resolve eq91 eq21218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq21218
  have eq21259 : ∀ X0 : G, y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq21220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21220
  have eq21273 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq21259 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq21259 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq21259 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21259
  have eq22996 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq21273 X0
       grind)
    | (have i₁ := eq44
       have i₂ := eq21273 x
       grind)
    | exact superpose eq21273 eq44
    | (have j1 := eq21273 X0
       grind)
    | exact resolve eq44 eq21273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq21273
  have eq23020 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq22996
    | (have j0 := eq22996 X0
       grind)
    | exact resolve eq22996 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22996
  have eq25133 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq19588
       have i₂ := eq23020 (k sF2 sF3)
       grind)
    | exact superpose eq23020 eq19588
    | (have j1 := eq23020 X0
       grind)
    | exact resolve eq19588 eq23020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19588 eq23020
  have eq25141 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq25133 X0
       grind)
    | (have r₁ := eq25133 X0
       have r₂ := eq27
       grind)
    | exact resolve eq25133 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25133
  have eq30581 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq25141 (M.op X0 X0)
       grind)
    | exact superpose eq25141 eq86
    | (have j1 := eq25141 X1
       grind)
    | exact resolve eq86 eq25141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq25141
  have eq47109 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3667 y
       have i₂ := eq30581 X0 y
       grind)
    | exact superpose eq30581 eq3667
    | (have j0 := eq3667 y
       have j1 := eq30581 X0 x
       grind)
    | exact resolve eq3667 eq30581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667 eq30581
  have eq47184 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq47109 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47109
  have eq47239 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq47184 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47184
    | (have j0 := eq47184 X0
       grind)
    | exact resolve eq47184 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq47184
  have eq47339 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq47239 X0
       have j1 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq47239 X0
       have r₂ := eq13 X0 (σ y)
       grind)
    | exact resolve eq47239 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47239
  have eq47431 : (τ (σ y)) = (k y y) := by
    first
    | exact superpose eq47339 eq125
    | exact resolve eq125 eq47339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq47447 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq47339 eq95
    | (have j0 := eq95 (σ y)
       grind)
    | exact resolve eq95 eq47339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq47339
  have eq47526 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq47447
  have eq47588 : y = (k y y) := by
    first
    | exact superpose eq29 eq47431
    | exact resolve eq47431 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq47431
  have eq48299 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq47526 eq60
    | exact resolve eq60 eq47526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47526
  have eq48966 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq19913 y y
       have i₂ := eq47588
       grind)
    | exact superpose eq47588 eq19913
    | (have j0 := eq19913 x y
       grind)
    | exact resolve eq19913 eq47588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19913 eq47588
  have eq48967 : y = (M.op y y) := by grind
  clear eq48966
  have eq49964 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq48299
    | (have j0 := eq48299 (σ x)
       grind)
    | exact resolve eq48299 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq48299
  have eq50029 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq49964 eq27
    | exact resolve eq27 eq49964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq49964
  have eq51865 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq60 y X0
       have i₂ := eq48967
       grind)
    | exact superpose eq48967 eq60
    | exact resolve eq60 eq48967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq48967
  have eq53976 : x = (M.op x y) := by
    first
    | (have i₁ := eq51865 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq51865
    | (have j0 := eq51865 x
       grind)
    | exact resolve eq51865 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq51865
  have eq54030 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq53976 eq20
    | exact resolve eq20 eq53976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq53976
  have eq54227 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq54030
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54030
    | exact resolve eq54030 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq54030
  have eq54265 : False := by grind
  exact eq54265

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_pyx_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq21 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq21 X0 (M.op X0 X0)
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq21 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq33
    | exact resolve eq33 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq60 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X1 X1)
       have i₂ := eq34 X1 (τ X0)
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq65 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq97 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq115 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (M.op X1 X1)
       have i₂ := eq34 X1 (σ X0)
       grind)
    | exact superpose eq34 eq97
    | exact resolve eq97 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq129 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq115
    | exact resolve eq115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq139 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45 x y
       grind)
    | exact superpose eq45 eq16
    | (have j1 := eq45 x y
       grind)
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq45 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq45 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq45 X0 X1
       grind)
    | exact resolve eq12 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (σ X0) X1
       have i₂ := eq45 X0 X0
       grind)
    | exact superpose eq45 eq21
    | (have j1 := eq45 X0 X0
       grind)
    | exact resolve eq21 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq151 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq45 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq152 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq151 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq158 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq160 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq162 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq160 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq160 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq527 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq152 (M.op X0 X0)
       have i₂ := eq34 X0 (M.op X0 X0)
       grind)
    | exact superpose eq34 eq152
    | (have j0 := eq152 (M.op X0 X0)
       grind)
    | exact resolve eq152 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq554 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have j0 := eq527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq625 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq158 X0 X2
       grind)
    | exact superpose eq158 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq158 X0 X2
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq158 X0 X1
       grind)
    | (have r₁ := eq12 X0 (σ (k X0 X0))
       have r₂ := eq158 X0 (σ (k X0 X0))
       grind)
    | exact resolve eq12 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq644 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq625 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq738 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq162 (M.op X0 X0) X1
       have i₂ := eq34 X0 (M.op X0 X0)
       grind)
    | exact superpose eq34 eq162
    | (have j0 := eq162 (M.op X0 X0) X1
       grind)
    | exact resolve eq162 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq755 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq162 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq162
    | (have j0 := eq162 (τ X0) X1
       grind)
    | exact resolve eq162 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq162
  have eq769 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq738 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq771 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq755 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq755
    | (have j0 := eq755 X0 X1
       grind)
    | exact resolve eq755 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq786 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq769 X0 X1
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq769
    | exact resolve eq769 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq769
  have eq787 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq771 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq771
    | (have j0 := eq771 X0 X1
       grind)
    | exact resolve eq771 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq1478 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq139
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq139
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq139 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq1479 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1478
  have eq5159 : ∀ X0 X1 X2 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X2 (σ (k X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq644 X1 X0 X2
       grind)
    | exact superpose eq644 eq64
    | (have j1 := eq644 X1 X1 X2
       grind)
    | exact resolve eq64 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq644
  have eq16540 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq554 y
       have i₂ := eq1479
       grind)
    | exact superpose eq1479 eq554
    | exact resolve eq554 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq16560 : y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq16540
  have eq105929 : ∀ X0 X1 X2 : G, (k X1 (k (τ (σ X0)) X0)) = X1 ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 X1 (σ X0)
       have i₂ := eq5159 (σ X0) X0 X2
       grind)
    | exact superpose eq5159 eq129
    | (have j1 := eq5159 X0 X0 X2
       grind)
    | exact resolve eq129 eq5159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5159
  have eq106117 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (k X1 (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105929 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105929
    | (have j0 := eq105929 X0 X1 X2
       grind)
    | exact resolve eq105929 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105929
  have eq106293 : ∀ X0 X1 X2 : G, (k X1 (τ (σ (k X0 X0)))) = X1 ∨ (k X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq129 X1 (σ (k X0 X0))
       have i₂ := eq106117 X0 X2 (σ (k X0 X0))
       grind)
    | exact superpose eq106117 eq129
    | (have j1 := eq106117 X0 X2 X2
       grind)
    | exact resolve eq129 eq106117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106117
  have eq106369 : ∀ X0 X1 X2 : G, (k X1 (k X0 X0)) = X1 ∨ (k X2 (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106293 X0 X1 X2
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq106293
    | (have j0 := eq106293 X0 X1 X1
       grind)
    | exact resolve eq106293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106293
  have eq107503 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq106369 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106369
  have eq107504 : ∀ X0 X1 : G, (k X0 (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq107503 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107503
  have eq107680 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq787 (k X0 X0) X1
       have i₂ := eq107504 (k X0 X0) X0
       grind)
    | exact superpose eq107504 eq787
    | (have j0 := eq787 (k X0 X0) X1
       grind)
    | (have r₁ := eq787 (k X1 X1) X1
       have r₂ := eq107504 (k X1 X1) X1
       grind)
    | exact resolve eq787 eq107504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq107968 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq107680 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107680
  have eq108025 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq107968 X0 X1
       have i₂ := eq107504 X1 X0
       grind)
    | exact superpose eq107504 eq107968
    | exact resolve eq107968 eq107504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107504 eq107968
  have eq108828 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq786 (k X0 X0) X1
       have i₂ := eq108025 X0 (k X0 X0)
       grind)
    | exact superpose eq108025 eq786
    | exact resolve eq786 eq108025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq162963 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq554 x
       have i₂ := eq16560
       grind)
    | exact superpose eq16560 eq554
    | exact resolve eq554 eq16560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq16560
  have eq163009 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq162963
  have eq163140 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq129 X0 (σ y)
       have i₂ := eq163009
       grind)
    | exact superpose eq163009 eq129
    | exact resolve eq129 eq163009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163009
  have eq163201 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq163140 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq163140
    | exact resolve eq163140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163140
  have eq164037 : ∀ X0 X1 : G, (k X0 (τ (σ y))) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq129 X0 (σ x)
       have i₂ := eq163201 X1
       grind)
    | exact superpose eq163201 eq129
    | (have j1 := eq163201 X1
       grind)
    | exact resolve eq129 eq163201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq163201
  have eq164122 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq164037 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq164037
    | (have j0 := eq164037 X0 X0
       grind)
    | exact resolve eq164037 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164037
  have eq166122 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq164122 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164122
  have eq166123 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq166122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166122
  have eq166419 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq108025 y X0
       have i₂ := eq166123 y
       grind)
    | exact superpose eq166123 eq108025
    | exact resolve eq108025 eq166123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108025
  have eq166442 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq108828 y X0
       have i₂ := eq166123 y
       grind)
    | exact superpose eq166123 eq108828
    | exact resolve eq108828 eq166123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108828 eq166123
  have eq169482 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq166442 (σ x)
       grind)
    | exact superpose eq166442 eq16
    | exact resolve eq16 eq166442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166442
  have eq169497 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq169482
       have i₂ := eq166419 x
       grind)
    | exact superpose eq166419 eq169482
    | exact resolve eq169482 eq166419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166419 eq169482
  have eq169498 : False := by grind
  exact eq169498

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq37 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq39 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq42 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq42
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq49
  have eq138 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq142 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq138 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq138 X1 X1
       have r₂ := eq54 X1 X1
       grind)
    | exact resolve eq138 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq138
  have eq277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq142 (σ X0) (σ X1)
       grind)
    | exact superpose eq142 eq15
    | exact resolve eq15 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 X1
       have i₂ := eq142 X0 X1
       grind)
    | exact superpose eq142 eq277
    | exact resolve eq277 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq277
  have eq288 : False := by grind
  exact eq288

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 (M.op x x))
       have i₂ := eq9 X0 (M.op X0 (M.op x x)) x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 X1) X0
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq19
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact superpose eq20 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq20 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq33 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq20 X0 X1
       grind)
    | exact superpose eq20 eq32
    | exact resolve eq32 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X0)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq19 X0 X1
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X1 X0)) ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq67 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (τ X0)
       grind)
    | exact superpose eq33 eq17
    | exact resolve eq17 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq71 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq67
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq108 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq70
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (τ (k (k X0 (σ X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq105
    | exact resolve eq105 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (M.op X1 X1)
       have i₂ := eq33 X1 (σ X0)
       grind)
    | exact superpose eq33 eq105
    | exact resolve eq105 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq123 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq123
    | exact resolve eq123 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq144 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq74
    | exact resolve eq74 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq74 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq74 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq74 X0 X1
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (M.op X1 (σ (k X0 X0))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) X1
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq20
    | (have j1 := eq74 X0 X0
       grind)
    | exact resolve eq20 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq165 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 (σ (k X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq166 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq169 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq166 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq166 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq166 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq177 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (τ (M.op X1 X1))
       have i₂ := eq136 (σ X0) X1
       grind)
    | exact superpose eq136 eq105
    | exact resolve eq105 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (k X0 (τ (τ (M.op X1 X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177
    | exact resolve eq177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq653 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (σ X0)
       have i₂ := eq165 X0 X1
       grind)
    | exact superpose eq165 eq30
    | (have j1 := eq165 X0 X2
       grind)
    | exact resolve eq30 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq764 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq169 (M.op X0 X0) X1
       have i₂ := eq33 X0 (M.op X0 X0)
       grind)
    | exact superpose eq33 eq169
    | (have j0 := eq169 (M.op X0 X0) X1
       grind)
    | exact resolve eq169 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 : G, (σ (τ (τ (M.op X0 X0)))) ≠ (σ (τ (τ (M.op X0 X0)))) ∨ (k X1 (σ (τ (τ (M.op X0 X0))))) = (M.op X1 (σ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq169 (τ (τ (M.op X0 X0))) X1
       have i₂ := eq185 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq185 eq169
    | (have j0 := eq169 (τ (τ (M.op X0 X0))) X1
       grind)
    | exact resolve eq169 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq185
  have eq787 : ∀ X0 X1 : G, (k X1 (σ (τ (τ (M.op X0 X0))))) = (M.op X1 (σ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have j0 := eq772 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq795 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq764 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq804 : ∀ X0 X1 : G, (k X1 (τ (M.op X0 X0))) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq787 X0 X1
       have i₂ := eq11 (τ (M.op X0 X0))
       grind)
    | exact superpose eq11 eq787
    | exact resolve eq787 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq812 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq71 X1 X0
       grind)
    | exact superpose eq71 eq795
    | exact resolve eq795 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq820 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq804 X0 X1
       have i₂ := eq136 X1 X0
       grind)
    | exact superpose eq136 eq804
    | exact resolve eq804 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq804
  have eq888 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op (τ (M.op X1 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (τ (M.op X1 X1)) X0
       have i₂ := eq820 X1 X0
       grind)
    | exact superpose eq820 eq19
    | exact resolve eq19 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq921 : ∀ X0 X1 X2 : G, (k X1 (M.op X0 X1)) = X1 ∨ (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 (M.op X0 X1) X2
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq33
    | (have j1 := eq48 X1 X0
       grind)
    | exact resolve eq33 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq48
  have eq1265 : ∀ X0 X1 X2 : G, (τ (k (k X0 (σ X1)) X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 (M.op (τ X0) X1) X2
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq105
    | (have j1 := eq76 X0 X1
       grind)
    | exact resolve eq105 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1276 : ∀ X0 X1 X2 : G, (k (k (τ X0) X1) (τ X2)) = (k (M.op (τ X0) X1) (τ X2)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1265 X0 X1 X2
       have i₂ := eq120 X0 X1 X2
       grind)
    | exact superpose eq120 eq1265
    | (have j0 := eq1265 X0 X1 X2
       grind)
    | exact resolve eq1265 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1265
  have eq1497 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (M.op X2 (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq888 X0 (σ X0)
       have i₂ := eq165 X0 X1
       grind)
    | exact superpose eq165 eq888
    | (have j1 := eq165 X0 X2
       grind)
    | exact resolve eq888 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq888
  have eq1559 : ∀ X0 X1 X2 : G, (M.op X2 (σ (k X0 X0))) = X2 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1497 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1497
    | (have j0 := eq1497 X0 X1 X2
       grind)
    | exact resolve eq1497 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq2670 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (σ X0)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (k X1 (σ X2)) (σ X0)
       have i₂ := eq144 X1 X2 X0
       grind)
    | exact superpose eq144 eq19
    | (have j1 := eq144 X1 X2 X0
       grind)
    | exact resolve eq19 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq3817 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (σ (k X0 X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq1559 X0 (σ (k X0 X0)) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq3818 : ∀ X0 : G, (M.op X0 (σ (k X0 X0))) = X0 := by
    intro X0
    first
    | (have j0 := eq3817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817
  have eq3874 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 (σ (k X0 X0)) X0
       have i₂ := eq3818 X0
       grind)
    | exact superpose eq3818 eq19
    | exact resolve eq19 eq3818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3818
  have eq4260 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq921 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq4261 : ∀ X0 X1 : G, (k X0 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4260 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4260
  have eq4278 : ∀ X0 : G, (k X0 (σ (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq4261 X0 (σ (k X0 X0))
       have i₂ := eq3874 X0
       grind)
    | exact superpose eq3874 eq4261
    | exact resolve eq4261 eq3874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3874
  have eq4288 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4261 (M.op X1 X1) X0
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq4261
    | exact resolve eq4261 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4329 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (M.op X1 (σ X0))
       have i₂ := eq4261 (σ X0) X1
       grind)
    | exact superpose eq4261 eq105
    | exact resolve eq105 eq4261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq4261
  have eq4335 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4329 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4329
    | exact resolve eq4329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4329
  have eq5726 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq653 X0 (σ (k X0 X0)) (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq5727 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq5726 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5726
  have eq5801 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq4335 (k X0 X0) (σ X0)
       have i₂ := eq5727 X0
       grind)
    | exact superpose eq5727 eq4335
    | exact resolve eq4335 eq5727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5727
  have eq5817 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq5801 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5801
    | exact resolve eq5801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5801
  have eq23552 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5817 (τ X0)
       have i₂ := eq1276 X0 (τ X0) X0
       grind)
    | exact superpose eq1276 eq5817
    | (have j1 := eq1276 X0 (τ X0) x
       grind)
    | exact resolve eq5817 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276 eq5817
  have eq23588 : ∀ X0 : G, (k (τ X0) (τ X0)) = (k (M.op (τ X0) (τ X0)) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq23552 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23552
  have eq23614 : ∀ X0 : G, (k (τ X0) (τ X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23588 X0
       have i₂ := eq4288 (τ X0) (τ X0)
       grind)
    | exact superpose eq4288 eq23588
    | (have j0 := eq23588 X0
       grind)
    | exact resolve eq23588 eq4288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288 eq23588
  have eq23640 : ∀ X0 : G, (k (τ X0) (τ X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq23614 X0
       have j1 := eq12 (τ X0) (τ X0)
       grind)
    | (have r₁ := eq23614 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq23614 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23614
  have eq23647 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23640 X0
       have i₂ := eq108 X0 X0
       grind)
    | exact superpose eq108 eq23640
    | exact resolve eq23640 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq23640
  have eq23658 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq23647 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23647
    | exact resolve eq23647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23718 : ∀ X0 X1 : G, (k X1 (σ (τ (k X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 X1 (τ X0)
       have i₂ := eq23647 X0
       grind)
    | exact superpose eq23647 eq71
    | exact resolve eq71 eq23647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq23647
  have eq23807 : ∀ X0 X1 : G, (k X1 (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23718 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq23718
    | exact resolve eq23718 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23718
  have eq23821 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq23658 X0
       have i₂ := eq70 (σ X0) X0
       grind)
    | exact superpose eq70 eq23658
    | exact resolve eq23658 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq23658
  have eq23828 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq23821 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23821
    | exact resolve eq23821 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23821
  have eq24572 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq23828 (σ X0)
       grind)
    | exact superpose eq23828 eq15
    | exact resolve eq15 eq23828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24637 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24572 X0
       have i₂ := eq23828 X0
       grind)
    | exact superpose eq23828 eq24572
    | exact resolve eq24572 eq23828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23828 eq24572
  have eq58126 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op (σ X1) X0) = (σ (k X1 (k (τ X0) (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2670 X0 X0 (k X0 X0)
       have i₂ := eq4278 X0
       grind)
    | exact superpose eq4278 eq2670
    | exact resolve eq2670 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670 eq4278
  have eq58254 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq58126 X0 X1
       have i₂ := eq23807 X0 (τ X0)
       grind)
    | exact superpose eq23807 eq58126
    | (have j0 := eq58126 X0 X1
       grind)
    | exact resolve eq58126 eq23807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23807 eq58126
  have eq58328 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq58254 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq58254
    | (have j0 := eq58254 X0 X1
       grind)
    | exact resolve eq58254 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq58254
  have eq58377 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq58328 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq58328 (σ X1) X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq58328 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq58328 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58328
  have eq119350 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58377 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58377
    | exact resolve eq58377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119386 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4335 X1 X0
       have i₂ := eq58377 X0 X1
       grind)
    | exact superpose eq58377 eq4335
    | (have j1 := eq58377 X0 X1
       grind)
    | exact resolve eq4335 eq58377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4335 eq58377
  have eq120885 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq119386 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq119386
    | (have j0 := eq119386 (σ X0) X1
       grind)
    | exact resolve eq119386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121170 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq119386 X1 (τ X0)
       grind)
    | exact superpose eq119386 eq17
    | (have j1 := eq119386 X1 (τ X0)
       grind)
    | exact resolve eq17 eq119386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq119386
  have eq121233 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq121170 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq121170
    | (have j0 := eq121170 X0 X1
       grind)
    | exact resolve eq121170 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121170
  have eq121491 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq120885 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq120885
    | (have j0 := eq120885 X0 X1
       grind)
    | exact resolve eq120885 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120885
  have eq121508 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq121233 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq121233
    | (have j0 := eq121233 X0 X1
       grind)
    | exact resolve eq121233 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121233
  have eq121658 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq121508 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq121508
    | (have j0 := eq121508 X0 X1
       grind)
    | exact resolve eq121508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121508
  have eq122713 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq121658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125961 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq121491 y x
       grind)
    | exact superpose eq121491 eq16
    | (have j1 := eq121491 y x
       grind)
    | exact resolve eq16 eq121491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121491
  have eq126642 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq125961
       have i₂ := eq121658 x y
       grind)
    | exact superpose eq121658 eq125961
    | (have j1 := eq121658 x y
       grind)
    | exact resolve eq125961 eq121658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121658
  have eq126643 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq125961
       have i₂ := eq119350 x y
       grind)
    | exact superpose eq119350 eq125961
    | (have j1 := eq119350 y x
       grind)
    | exact resolve eq125961 eq119350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119350 eq125961
  have eq126653 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq126643
  have eq126654 : x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq126642
  have eq126657 : x = (k x y) := by
    first
    | (have j1 := eq122713 x y
       grind)
    | (have r₁ := eq126654
       have r₂ := eq122713 x y
       grind)
    | exact resolve eq126654 eq122713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122713 eq126654
  have eq127026 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq157 x y
       have i₂ := eq126657
       grind)
    | exact superpose eq126657 eq157
    | (have j0 := eq157 x y
       grind)
    | exact resolve eq157 eq126657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq126657
  have eq127036 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq127026
  have eq127040 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq127036
       have i₂ := eq24637 y
       grind)
    | exact superpose eq24637 eq127036
    | exact resolve eq127036 eq24637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24637 eq127036
  have eq127188 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19 x y
       have i₂ := eq126653
       grind)
    | exact superpose eq126653 eq19
    | exact resolve eq19 eq126653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq126653
  have eq127208 : x = (M.op x y) := by grind
  clear eq127188
  have eq144188 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127040
       grind)
    | exact superpose eq127040 eq16
    | exact resolve eq16 eq127040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127040
  have eq144247 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq144188
       have i₂ := eq127208
       grind)
    | exact superpose eq127208 eq144188
    | exact resolve eq144188 eq127208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127208 eq144188
  have eq144248 : (σ y) = (σ (M.op y y)) := by grind
  clear eq144247
  have eq144270 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq812 y X0
       have i₂ := eq144248
       grind)
    | exact superpose eq144248 eq812
    | exact resolve eq812 eq144248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq144283 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq144248
       grind)
    | exact superpose eq144248 eq10
    | exact resolve eq10 eq144248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144248
  have eq144570 : y = (M.op y y) := by
    first
    | (have i₁ := eq144283
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq144283
    | exact resolve eq144283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144283
  have eq145337 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 y X0
       have i₂ := eq144570
       grind)
    | exact superpose eq144570 eq20
    | exact resolve eq20 eq144570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq144570
  have eq149500 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq144270 (σ x)
       grind)
    | exact superpose eq144270 eq16
    | exact resolve eq16 eq144270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144270
  have eq149505 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq149500
       have i₂ := eq145337 x
       grind)
    | exact superpose eq145337 eq149500
    | exact resolve eq149500 eq145337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145337 eq149500
  have eq149506 : False := by grind
  exact eq149506
