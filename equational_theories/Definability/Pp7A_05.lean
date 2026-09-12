import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1460`: `x = (x ◇ y) ◇ (y ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_pyy_pxy_Equation1460 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1460 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  clear eq36
  have eq51 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
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
  have eq52 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op x y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) X2 (M.op x x)
       have i₂ := eq14 X0 X2 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq83 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq90 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq83
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq101 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq101
  have eq120 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq106
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq120
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq186 : (σ (k (k y y) y)) = (k (k (σ y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq41
    | exact resolve eq41 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (σ (k (k (M.op x y) (M.op x y)) y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq134 eq41
    | exact resolve eq41 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq134
  have eq211 : ∀ X0 : G, x = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq224 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq284 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq215 eq56
    | exact resolve eq56 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, (M.op x y) = (M.op x (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq211 eq56
    | exact resolve eq56 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq224 eq56
    | exact resolve eq56 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 := by
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
  have eq299 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) X0 (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq318 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq230 eq56
    | exact resolve eq56 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op X0 (M.op X1 X2)) X1
       have i₂ := eq57 X1 X0 X2
       grind)
    | exact superpose eq57 eq54
    | exact resolve eq54 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X2 (M.op X0 (M.op X1 X3)) X1
       have i₂ := eq57 X1 X0 X3
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq412 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq554 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq555 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ (k X0 X1))) (σ X0)) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (σ X0) X2 (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq57
    | (have j1 := eq77 X0 X1
       grind)
    | exact resolve eq57 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq572 : ∀ X0 : G, (k (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq554 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq573 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq555
    | (have j0 := eq555 X0 X1
       grind)
    | exact resolve eq555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq574 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq572 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq572
    | (have j0 := eq572 X0
       grind)
    | exact resolve eq572 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq618 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq392 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq392
    | (have j0 := eq392 X0 y
       grind)
    | exact resolve eq392 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21 eq392
    | (have j0 := eq392 X0 (M.op x y)
       grind)
    | exact resolve eq392 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq1381 : (k (k y y) y) = (τ (k (k (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq106 eq618
    | exact resolve eq618 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1701 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq303 (σ x)
       have i₂ := eq77 x x
       grind)
    | exact superpose eq77 eq303
    | (have j1 := eq77 X0 X0
       grind)
    | exact resolve eq303 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1706 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701
  have eq1707 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1706 X0
       have i₂ := eq10 X0 (k X0 X0)
       grind)
    | exact superpose eq10 eq1706
    | (have j0 := eq1706 X0
       grind)
    | exact resolve eq1706 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq3664 : (k (k (σ y) (σ y)) (σ y)) = (σ (k (M.op y y) y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq186
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq186
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq186 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3681 : (k (k (σ y) (σ y)) (σ y)) = (σ (k (M.op y y) y)) ∨ y = (M.op y y) := by grind
  clear eq3664
  have eq3682 : (k (k (σ y) (σ y)) (σ y)) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) := by grind
  clear eq3681
  have eq4901 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq412 X0
       have i₂ := eq343 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq343 eq412
    | exact resolve eq412 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq412
  have eq5025 : ∀ X0 : G, (σ (M.op (τ (σ X0)) (M.op (τ (σ X0)) (M.op x y)))) = (σ (k (M.op (τ (σ X0)) (τ (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ (σ X0)) (τ (σ X0))) X0
       have i₂ := eq4901 (σ X0)
       grind)
    | exact superpose eq4901 eq10
    | exact resolve eq10 eq4901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4901
  have eq5049 : ∀ X0 : G, (σ (M.op X0 (M.op X0 (M.op x y)))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5025 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq5025
    | exact resolve eq5025 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5025
  have eq5073 : ∀ X0 : G, (σ (M.op X0 (M.op X0 (M.op x y)))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq5049
  have eq5471 : ∀ X0 X1 X2 : G, (M.op X1 (σ (k y X0))) = (M.op X1 (M.op (σ y) X2)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq79 eq345
    | (have j1 := eq79 X0
       grind)
    | exact resolve eq345 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq8139 : ∀ X0 : G, (σ X0) = (M.op (σ (k (k X0 X0) X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq566 X0 X0 (σ X0)
       have i₂ := eq574 X0
       grind)
    | exact superpose eq574 eq566
    | (have j0 := eq566 X0 X0 x
       have j1 := eq574 X0
       grind)
    | exact resolve eq566 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq8250 : ∀ X0 : G, (σ X0) = (M.op (σ (k (k X0 X0) X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq8139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8139
  have eq16182 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 (M.op x y)))) = (σ (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq5073 X0
       have i₂ := eq345 X0 X0 X0 X1
       grind)
    | (have i₁ := eq5073 X0
       have i₂ := eq345 X0 X0 X1 X0
       grind)
    | exact superpose eq345 eq5073
    | exact resolve eq5073 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq5073
  have eq22063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq22064 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq22063
    | exact resolve eq22063 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22063
  have eq22075 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq22064
       have r₂ := eq28
       grind)
    | exact resolve eq22064 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22064
  have eq22077 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22075 eq122
    | exact resolve eq122 eq22075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq22097 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq22075 eq56
    | exact resolve eq56 eq22075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq22124 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq22077
    | exact resolve eq22077 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22077
  have eq24146 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22075 eq22097
    | exact resolve eq22097 eq22075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22075 eq22097
  have eq24213 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq24146
  have eq34574 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq22124 eq290
    | exact resolve eq290 eq22124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq34579 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22124 eq299
    | exact resolve eq299 eq22124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq22124
  have eq34629 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq318 eq34574
    | (have j0 := eq34574 (σ y)
       grind)
    | exact resolve eq34574 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq34574
  have eq35744 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq34629 eq34579
    | exact resolve eq34579 eq34629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34579 eq34629
  have eq35788 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq35744
  have eq35828 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq35788
       grind)
    | exact superpose eq35788 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq35788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35829 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq35828
  have eq36149 : (k y y) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq303 y
       have i₂ := eq35829
       grind)
    | exact superpose eq35829 eq303
    | exact resolve eq303 eq35829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35829
  have eq39231 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq35788
       have i₂ := eq36149
       grind)
    | exact superpose eq36149 eq35788
    | exact resolve eq35788 eq36149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35788 eq36149
  have eq39246 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq39231
  have eq39546 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq39246
       grind)
    | exact superpose eq39246 eq107
    | exact resolve eq107 eq39246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq39552 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq303 y
       have i₂ := eq39246
       grind)
    | exact superpose eq39246 eq303
    | exact resolve eq303 eq39246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39246
  have eq39592 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq39552
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq39552
    | exact resolve eq39552 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39552
  have eq39596 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq39546
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39546
    | exact resolve eq39546 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39546
  have eq39920 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq39592
       grind)
    | exact superpose eq39592 eq74
    | exact resolve eq74 eq39592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39592
  have eq39955 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq21 eq39920
    | exact resolve eq39920 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39920
  have eq46816 : (τ (σ x)) = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq39596 eq106
    | exact resolve eq106 eq39596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq46854 : x = (k y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq46816
    | exact resolve eq46816 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46816
  have eq140096 : ∀ X0 : G, (M.op (σ (k (k (τ X0) (τ X0)) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq8250 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq8250
    | exact resolve eq8250 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8250
  have eq140380 : ∀ X0 : G, (M.op (k (σ (k (τ X0) (τ X0))) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq140096 X0
       have i₂ := eq39 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq39 eq140096
    | (have j0 := eq140096 X0
       grind)
    | exact resolve eq140096 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq140096
  have eq140425 : ∀ X0 : G, (M.op (k (k X0 (σ (τ X0))) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq140380 X0
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq140380
    | (have j0 := eq140380 X0
       grind)
    | exact resolve eq140380 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq140380
  have eq140464 : ∀ X0 : G, (M.op (k (k X0 X0) X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq140425 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq140425
    | (have j0 := eq140425 X0
       grind)
    | exact resolve eq140425 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140425
  have eq149251 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1707 y
       have i₂ := eq46854
       grind)
    | exact superpose eq46854 eq1707
    | (have j0 := eq1707 y
       grind)
    | exact resolve eq1707 eq46854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707 eq46854
  have eq149652 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq149251
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq149251
    | exact resolve eq149251 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq149251
  have eq149698 : (k (σ y) (σ x)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq149652
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq149652
    | exact resolve eq149652 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149652
  have eq149736 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq149698
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq149698
    | exact resolve eq149698 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149698
  have eq149761 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq27 eq149736
    | exact resolve eq149736 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149736
  have eq149777 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq149761
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq149761
    | exact resolve eq149761 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149761
  have eq201160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq149777 eq39955
    | exact resolve eq39955 eq149777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39955 eq149777
  have eq201202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq201160
  have eq201219 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq201202
       have r₂ := eq28
       grind)
    | exact resolve eq201202 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201202
  have eq201261 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  have eq204646 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq201261 eq39596
    | exact resolve eq39596 eq201261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39596 eq201261
  have eq204683 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq204646
  have eq204713 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq204683 eq201219
    | exact resolve eq201219 eq204683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201219 eq204683
  have eq204824 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq204713
  have eq204853 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq287 x X0
       have i₂ := eq204824
       grind)
    | exact superpose eq204824 eq287
    | exact resolve eq287 eq204824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq204854 : y = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq296 y
       have i₂ := eq204824
       grind)
    | exact superpose eq204824 eq296
    | exact resolve eq296 eq204824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296 eq204824
  have eq204913 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq204853 x
       have i₂ := eq284 x x
       grind)
    | (have i₁ := eq204853 y
       have i₂ := eq284 x x
       grind)
    | exact superpose eq284 eq204853
    | (have j0 := eq204853 y
       grind)
    | exact resolve eq204853 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq204853
  have eq207959 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq204913 eq204854
    | exact resolve eq204854 eq204913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204854 eq204913
  have eq208022 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq207959
  have eq208103 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq208022 eq224
    | exact resolve eq224 eq208022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq208104 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ x)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq208022 eq230
    | exact resolve eq230 eq208022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq208022
  have eq212452 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq208103 eq208103
    | exact resolve eq208103 eq208103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212679 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq212452
  have eq285878 : ∀ X0 : G, (σ (k (k y y) y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq574 y
       have i₂ := eq5471 y (σ y) X0
       grind)
    | exact superpose eq5471 eq574
    | (have j0 := eq574 y
       have j1 := eq5471 y x x
       grind)
    | exact resolve eq574 eq5471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq5471
  have eq286219 : ∀ X0 : G, (σ (k (k y y) y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq285878 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq285878
    | (have j0 := eq285878 X0
       grind)
    | exact resolve eq285878 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285878
  have eq286298 : ∀ X0 : G, (k (k (σ y) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq286219 X0
       have i₂ := eq186
       grind)
    | exact superpose eq186 eq286219
    | exact resolve eq286219 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286219
  have eq286350 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k (k (σ y) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq286298 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq286298
    | (have j0 := eq286298 X0
       grind)
    | exact resolve eq286298 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286298
  have eq286369 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (k (σ y) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq286350 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq286350
    | (have j0 := eq286350 X0
       grind)
    | exact resolve eq286350 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286350
  have eq286370 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k (k (σ y) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq286369 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286369
  have eq286379 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (k (σ y) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq286370 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq286370
    | (have j0 := eq286370 X0
       grind)
    | exact resolve eq286370 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286370
  have eq286380 : ∀ X0 : G, (k (k (σ y) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq286379 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286379
  have eq2861681 : (σ x) = (k (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq208103 eq286380
    | exact resolve eq286380 eq208103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208103 eq286380
  have eq2862243 : (τ (σ x)) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2861681 eq1381
    | exact resolve eq1381 eq2861681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381 eq2861681
  have eq2862402 : x = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq2862243
    | exact resolve eq2862243 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862243
  have eq2862642 : y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq140464 y
       have i₂ := eq2862402
       grind)
    | exact superpose eq2862402 eq140464
    | (have j0 := eq140464 y
       grind)
    | exact resolve eq140464 eq2862402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862402
  have eq2862741 : y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2862642
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2862642
    | exact resolve eq2862642 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862642
  have eq2862742 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2862741
  have eq2863203 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2862742 eq208104
    | exact resolve eq208104 eq2862742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862742
  have eq2863408 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq2863203
  have eq2863964 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq2863408 eq212679
    | exact resolve eq212679 eq2863408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863408
  have eq2864595 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2863964
  have eq2864952 : (k y y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  have eq2864971 : y = (M.op y (M.op y (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq54 y y
       have i₂ := eq2864595
       grind)
    | exact superpose eq2864595 eq54
    | exact resolve eq54 eq2864595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq2864595
  have eq2867121 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq2864952
       grind)
    | exact superpose eq2864952 eq75
    | exact resolve eq75 eq2864952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq2864952
  have eq2867934 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2864971 eq16182
    | exact resolve eq16182 eq2864971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16182 eq2864971
  have eq2868158 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2867934
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2867934
    | exact resolve eq2867934 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2867934
  have eq2870417 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2868158
       have i₂ := eq2867121
       grind)
    | exact superpose eq2867121 eq2868158
    | exact resolve eq2868158 eq2867121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2867121 eq2868158
  have eq2870947 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2870417
  have eq2871217 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2870947 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq2870947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2870947
  have eq2871300 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2871217
  have eq2871557 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2871300 eq208104
    | exact resolve eq208104 eq2871300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208104 eq2871300
  have eq2871762 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2871557
  have eq2873236 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2871762 eq212679
    | exact resolve eq212679 eq2871762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212679 eq2871762
  have eq2873867 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2873236
  have eq2874105 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2873867 eq30
    | exact resolve eq30 eq2873867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2873867
  have eq2874658 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2874105
    | exact resolve eq2874105 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874105
  have eq2874659 : y = (M.op x y) ∨ x = y := by grind
  clear eq2874658
  have eq2874661 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2874659 eq21
    | exact resolve eq21 eq2874659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2874703 : (σ (k (k y y) y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2874659 eq190
    | exact resolve eq190 eq2874659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq2874713 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2874659 eq211
    | exact resolve eq211 eq2874659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq2874714 : ∀ X0 : G, (M.op (M.op X0 y) x) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq2874659 eq215
    | exact resolve eq215 eq2874659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq2874738 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2874659 eq619
    | exact resolve eq619 eq2874659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq2877532 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2874738 X0
       have i₂ := eq618 X0
       grind)
    | exact superpose eq618 eq2874738
    | exact resolve eq2874738 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq2874738
  have eq2877553 : (k (k (σ y) (σ y)) (σ y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2874703
       have i₂ := eq186
       grind)
    | exact superpose eq186 eq2874703
    | exact resolve eq2874703 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq2874703
  have eq2877590 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2874661
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2874661
    | exact resolve eq2874661 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874661
  have eq2879640 : x = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq2874713 (M.op y x)
       have i₂ := eq2874713 x
       grind)
    | exact superpose eq2874713 eq2874713
    | exact resolve eq2874713 eq2874713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2880226 : x = (M.op y x) ∨ x = y := by grind
  clear eq2879640
  have eq2936624 : ∀ X0 : G, (k X0 (σ y)) = (σ (τ (k X0 (σ (M.op x y))))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2877532 eq15
    | exact resolve eq15 eq2877532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2877532
  have eq2937956 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2936624 X0
       have i₂ := eq15 (k X0 sF1)
       grind)
    | exact superpose eq15 eq2936624
    | exact resolve eq2936624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936624
  have eq3445639 : (σ x) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3682
       have i₂ := eq2874713 y
       grind)
    | exact superpose eq2874713 eq3682
    | exact resolve eq3682 eq2874713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3682 eq2874713
  have eq3446295 : (σ x) = (k (k (σ y) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3445639
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3445639
    | exact resolve eq3445639 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445639
  have eq4447266 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = y ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq3446295 eq2877553
    | exact resolve eq2877553 eq3446295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2877553
  have eq4447325 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq3446295 eq140464
    | (have j0 := eq140464 (σ y)
       grind)
    | exact resolve eq140464 eq3446295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140464 eq3446295
  have eq4447417 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq4447266
  have eq4447463 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq4447325
    | exact resolve eq4447325 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4447325
  have eq5435024 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2877590 eq4447463
    | exact resolve eq4447463 eq2877590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2877590 eq4447463
  have eq5435493 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq5435024
  have eq5435530 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq5435493
       have r₂ := eq28
       grind)
    | exact resolve eq5435493 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5435493
  have eq5435581 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = y := by grind
  have eq5437306 : (σ x) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq5435581 eq4447417
    | exact resolve eq4447417 eq5435581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4447417
  have eq5437454 : (σ x) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq5437306
  have eq5443951 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq5435530 eq5437454
    | exact resolve eq5437454 eq5435530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5437454
  have eq5444118 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq5443951
  have eq5444392 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq5444118 eq2937956
    | exact resolve eq2937956 eq5444118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2937956 eq5444118
  have eq5444485 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ y = (M.op y y) := by grind
  clear eq5444392
  have eq5445800 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = y ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq5444485 eq5435581
    | exact resolve eq5435581 eq5444485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5435581 eq5444485
  have eq5445952 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op y y) ∨ x = y := by grind
  clear eq5445800
  have eq5451452 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) ∨ x = y ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq5445952 eq5435530
    | exact resolve eq5435530 eq5445952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5435530 eq5445952
  have eq5451770 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq5451452
  have eq5452058 : y = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2874714 y
       have i₂ := eq5451770
       grind)
    | exact superpose eq5451770 eq2874714
    | exact resolve eq2874714 eq5451770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874714 eq5451770
  have eq5452268 : y = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5452058
  have eq5454403 : x = y ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2880226
       have i₂ := eq5452268
       grind)
    | exact superpose eq5452268 eq2880226
    | exact resolve eq2880226 eq5452268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2880226 eq5452268
  have eq5455024 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq5454403
  have eq5455359 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq5455024 eq29
    | exact resolve eq29 eq5455024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5455024
  have eq5457840 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq5455359
    | exact resolve eq5455359 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5455359
  have eq5460902 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq5457840 eq2874659
    | exact resolve eq2874659 eq5457840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874659 eq5457840
  have eq5462891 : x = y := by grind
  clear eq5460902
  have eq5464783 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq5462891
       grind)
    | exact superpose eq5462891 eq19
    | exact resolve eq19 eq5462891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq5464784 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq5462891
       grind)
    | exact superpose eq5462891 eq25
    | exact resolve eq25 eq5462891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq5466436 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5464784
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5464784
    | exact resolve eq5464784 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5464784
  have eq5466464 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5466436 eq27
    | exact resolve eq27 eq5466436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq5468145 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq5464783
       grind)
    | exact superpose eq5464783 eq90
    | exact resolve eq90 eq5464783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq5468164 : (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq303 x
       have i₂ := eq5464783
       grind)
    | exact superpose eq5464783 eq303
    | exact resolve eq303 eq5464783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq5468426 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq5468145
    | exact resolve eq5468145 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5468145
  have eq5469071 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq5466464 eq24213
    | exact resolve eq24213 eq5466464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24213
  have eq5469091 : (M.op (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq5469417 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq5466436 eq5469071
    | exact resolve eq5469071 eq5466436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5469071
  have eq5469439 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq5466436 eq5469417
    | exact resolve eq5469417 eq5466436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5466436 eq5469417
  have eq5469449 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq5466464 eq5469439
    | exact resolve eq5469439 eq5466464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5469439
  have eq5469450 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq5469449
  have eq5469462 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5469450
       have i₂ := eq5462891
       grind)
    | exact superpose eq5462891 eq5469450
    | exact resolve eq5469450 eq5462891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5469450
  have eq5469476 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq5469462
       have i₂ := eq5464783
       grind)
    | exact superpose eq5464783 eq5469462
    | exact resolve eq5469462 eq5464783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5469462
  have eq5469483 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5469476
       have i₂ := eq5462891
       grind)
    | exact superpose eq5462891 eq5469476
    | exact resolve eq5469476 eq5462891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5462891 eq5469476
  have eq5469487 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5469483
       have i₂ := eq5464783
       grind)
    | exact superpose eq5464783 eq5469483
    | exact resolve eq5469483 eq5464783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5469483
  have eq5469488 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5469487
  have eq5472524 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5469488 eq5469091
    | exact resolve eq5469091 eq5469488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5469091 eq5469488
  have eq5472635 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5466464 eq5472524
    | exact resolve eq5472524 eq5466464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5472524
  have eq5481978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5472635 eq5468426
    | exact resolve eq5468426 eq5472635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5468426 eq5472635
  have eq5482112 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5481978
  have eq5482157 : x = (M.op x y) := by
    first
    | (have r₁ := eq5482112
       have r₂ := eq28
       grind)
    | exact resolve eq5482112 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5482112
  have eq5482257 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq5482157 eq21
    | exact resolve eq21 eq5482157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq5485265 : (k x x) = (M.op x x) := by
    first
    | exact superpose eq5482157 eq5468164
    | exact resolve eq5468164 eq5482157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5468164
  have eq5485340 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq5485265
       have i₂ := eq5464783
       grind)
    | exact superpose eq5464783 eq5485265
    | exact resolve eq5485265 eq5464783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5464783 eq5485265
  have eq5486057 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5482257
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5482257
    | exact resolve eq5482257 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5482257
  have eq5486060 : x = (k x x) := by
    first
    | exact superpose eq5482157 eq5485340
    | exact resolve eq5485340 eq5482157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5482157 eq5485340
  have eq5490325 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq573 x x
       have i₂ := eq5486060
       grind)
    | exact superpose eq5486060 eq573
    | (have j0 := eq573 x x
       grind)
    | exact resolve eq573 eq5486060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq5486060
  have eq5490407 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5490325
  have eq5490408 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5490407
  have eq5490470 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5490408
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5490408
    | exact resolve eq5490408 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq5490408
  have eq5490772 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5466464 eq5490470
    | exact resolve eq5490470 eq5466464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5466464 eq5490470
  have eq5491062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5486057 eq5490772
    | exact resolve eq5490772 eq5486057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5486057 eq5490772
  have eq5491342 : False := by grind
  exact eq5491342

/-- `Equation1465`: `x = (x ◇ y) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = m(Y,X) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyx_x_pyy_pxy_Equation1465 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1465 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1465.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X1 X0))) = X0 := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
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
  clear eq36
  have eq47 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) (σ x)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op (M.op X2 (M.op X1 X0)) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op X2 (M.op X1 X0)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, y = (M.op (M.op y x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X2)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X2 X0)) (M.op X0 X2) X3
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 (M.op X0 X1)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq69
    | exact resolve eq69 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq72
    | exact resolve eq72 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq112 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq152 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq112 eq16
    | exact resolve eq16 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq355 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op X2 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X2 (M.op X1 X0)) (M.op X0 X1) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, y = (M.op (M.op y X1) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X1) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq82 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq82
    | (have j0 := eq82 (σ X0)
       grind)
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq44
    | (have j1 := eq82 x
       grind)
    | exact resolve eq44 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq416 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq57
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq57
    | (have j1 := eq82 (σ x)
       grind)
    | exact resolve eq57 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq495 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq356 eq49
    | exact resolve eq49 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq496 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq357 eq49
    | exact resolve eq49 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 X1 X2 (M.op X0 (M.op X1 X2)) X3
       have i₂ := eq53 (M.op X1 X2) X0 (M.op X2 X1)
       grind)
    | exact superpose eq53 eq49
    | exact resolve eq49 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op (M.op X0 (M.op X1 x)) (M.op x X1))
       have i₂ := eq52 x X0 X1 y
       grind)
    | exact superpose eq52 eq47
    | exact resolve eq47 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op (M.op X1 (M.op x sF2)) (M.op sF2 x))
       have i₂ := eq52 sF2 X1 x sF3
       grind)
    | exact superpose eq52 eq48
    | exact resolve eq48 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : ∀ X1 X2 : G, (M.op x y) = (M.op x (M.op X1 (M.op X2 (M.op x y)))) := by
    intro X1 X2
    first
    | exact superpose eq47 eq355
    | exact resolve eq355 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1133 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 X1 (M.op X2 X0) X0 X3
       have i₂ := eq355 X0 X2 X1 (M.op (M.op X2 X0) X1)
       grind)
    | exact superpose eq355 eq49
    | exact resolve eq49 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq355
  have eq1421 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X0 (M.op X2 (M.op X1 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq1133
    | exact resolve eq1133 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1423 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X2 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq1133
    | exact resolve eq1133 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1925 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq497 (M.op (M.op X0 (M.op X1 X2)) (M.op X2 X1)) X3 X2 X4
       have i₂ := eq52 X2 X0 X1 X3
       grind)
    | exact superpose eq52 eq497
    | exact resolve eq497 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq5128 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op X1 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) x
       have i₂ := eq408 X0
       grind)
    | exact superpose eq408 eq14
    | (have j1 := eq408 X0
       grind)
    | exact resolve eq14 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5145 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq408 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq26256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq74 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq26256
    | exact resolve eq26256 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26256
  have eq26268 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq26257
       have r₂ := eq28
       grind)
    | exact resolve eq26257 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26257
  have eq26270 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq26268
    | exact resolve eq26268 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26268
  have eq26272 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26270 eq48
    | exact resolve eq48 eq26270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26273 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26270 eq51
    | exact resolve eq51 eq26270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26270
  have eq26660 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26273 eq26272
    | exact resolve eq26272 eq26273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26272 eq26273
  have eq26719 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq26660
  have eq26772 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26719 eq416
    | exact resolve eq416 eq26719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26776 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq26719
  have eq26817 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq26772
  have eq26843 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq26817
    | exact resolve eq26817 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26817
  have eq26856 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26776 eq61
    | exact resolve eq61 eq26776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26857 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26776 eq74
    | exact resolve eq74 eq26776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq26776
  have eq26865 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq26857
  have eq26873 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq29 eq26856
    | exact resolve eq26856 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26856
  have eq26876 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq26865
       grind)
    | exact superpose eq26865 eq47
    | exact resolve eq47 eq26865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26887 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq26865
       grind)
    | exact superpose eq26865 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq26865
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq26865
       grind)
    | exact resolve eq12 eq26865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26900 : ∀ X0 X1 : G, (M.op x y) = (M.op y (M.op X0 (M.op X1 (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq497 X0 y x x
       have i₂ := eq26865
       grind)
    | exact superpose eq26865 eq497
    | exact resolve eq497 eq26865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26865
  have eq26921 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq26887
  have eq26931 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1421 eq26900
    | exact resolve eq26900 eq1421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26900
  have eq26937 : (k x y) = (M.op y y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq26921
       have r₂ := eq19
       grind)
    | exact resolve eq26921 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26921
  have eq27201 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq26931
       grind)
    | exact superpose eq26931 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq26931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27235 : y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq27201
  have eq27724 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq26843
       grind)
    | exact superpose eq26843 eq47
    | exact resolve eq47 eq26843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27725 : ∀ X0 : G, y = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq26843
       grind)
    | exact superpose eq26843 eq50
    | exact resolve eq50 eq26843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq26843
  have eq27810 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq26873
       grind)
    | exact superpose eq26873 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq26873
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq26873
       grind)
    | exact resolve eq12 eq26873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27823 : ∀ X0 X1 : G, (M.op x y) = (M.op y (M.op X0 (M.op X1 (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq497 X0 y x x
       have i₂ := eq26873
       grind)
    | exact superpose eq26873 eq497
    | exact resolve eq497 eq26873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27841 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op X0 (M.op X1 (M.op X2 (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1925 X2 y x X0 X1
       have i₂ := eq26873
       grind)
    | exact superpose eq26873 eq1925
    | exact resolve eq1925 eq26873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925 eq26873
  have eq27844 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq27810
  have eq27845 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1421 eq27841
    | exact resolve eq27841 eq1421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27841
  have eq27854 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1421 eq27823
    | exact resolve eq27823 eq1421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27823
  have eq27860 : (k x y) = (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq27844
       have r₂ := eq19
       grind)
    | exact resolve eq27844 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27844
  have eq28491 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26876 eq1091
    | exact resolve eq1091 eq26876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26876
  have eq28618 : y ≠ (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq28491
  have eq32290 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq26937
       grind)
    | exact superpose eq26937 eq45
    | exact resolve eq45 eq26937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26937
  have eq34672 : (M.op x y) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq27235
       have r₂ := eq28618
       grind)
    | exact resolve eq27235 eq28618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27235 eq28618
  have eq34674 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq34672
       grind)
    | exact superpose eq34672 eq88
    | exact resolve eq88 eq34672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34672
  have eq34700 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq34674
    | exact resolve eq34674 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34674
  have eq34985 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq34700
       have i₂ := eq82 sF3
       grind)
    | exact superpose eq82 eq34700
    | (have j1 := eq82 (σ y)
       grind)
    | exact resolve eq34700 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35293 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq32290
       have i₂ := eq26931
       grind)
    | exact superpose eq26931 eq32290
    | exact resolve eq32290 eq26931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26931 eq32290
  have eq35396 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq35293
  have eq35404 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq35396
    | exact resolve eq35396 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35396
  have eq35430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35404 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq35404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35442 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq35430
    | exact resolve eq35430 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35430
  have eq35453 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq35442
       have r₂ := eq28
       grind)
    | exact resolve eq35442 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35442
  have eq35455 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq35453
    | exact resolve eq35453 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35453
  have eq42398 : x = y ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27725 eq27724
    | exact resolve eq27724 eq27725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27724 eq27725
  have eq42468 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq42398
  have eq42545 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq82 x
       have i₂ := eq42468
       grind)
    | exact superpose eq42468 eq82
    | (have j0 := eq82 x
       grind)
    | exact resolve eq82 eq42468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42546 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq42545
  have eq42866 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq632 X0 x
       have i₂ := eq42546
       grind)
    | exact superpose eq42546 eq632
    | exact resolve eq632 eq42546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42546
  have eq42952 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq42866 x
       have i₂ := eq495 sF0 x
       grind)
    | (have i₁ := eq42866 x
       have i₂ := eq495 sF0 x
       grind)
    | exact superpose eq495 eq42866
    | (have j0 := eq42866 x
       grind)
    | exact resolve eq42866 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42866
  have eq127924 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq27860
       grind)
    | exact superpose eq27860 eq45
    | exact resolve eq45 eq27860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128022 : x ≠ (M.op y y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq27860
  have eq128866 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq128022
       have i₂ := eq27854
       grind)
    | exact superpose eq27854 eq128022
    | exact resolve eq128022 eq27854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27854 eq128022
  have eq128877 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq128866
  have eq220643 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ (σ x) = (σ y) ∨ x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq127924
       have i₂ := eq27845 y
       grind)
    | exact superpose eq27845 eq127924
    | exact resolve eq127924 eq27845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27845 eq127924
  have eq220809 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq220643
  have eq222415 : (M.op y x) = (τ (k (σ x) (σ y))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq220809
       grind)
    | exact superpose eq220809 eq16
    | exact resolve eq16 eq220809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220809
  have eq222576 : (k x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | exact superpose eq61 eq222415
    | exact resolve eq222415 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222415
  have eq222590 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq222576
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq222576
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq222576 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222576
  have eq222813 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq222590
  have eq222823 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq222813
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq222813
    | exact resolve eq222813 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222813
  have eq222826 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq222823
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq222823
    | exact resolve eq222823 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222823
  have eq222829 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq222826
       grind)
    | exact superpose eq222826 eq47
    | exact resolve eq47 eq222826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq222874 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq222826
       grind)
    | exact superpose eq222826 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq222826
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq222826
       grind)
    | exact resolve eq12 eq222826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222887 : ∀ X0 X1 : G, (M.op x y) = (M.op y (M.op X0 (M.op X1 (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq497 X0 y x x
       have i₂ := eq222826
       grind)
    | exact superpose eq222826 eq497
    | exact resolve eq497 eq222826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222826
  have eq222913 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq222874
  have eq222955 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1421 eq222887
    | exact resolve eq222887 eq1421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421 eq222887
  have eq222961 : (k x y) = (M.op y y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq222913
       have r₂ := eq19
       grind)
    | exact resolve eq222913 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222913
  have eq222998 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq222955
       grind)
    | exact superpose eq222955 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq222955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223037 : y = (M.op x y) ∨ (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq222998
  have eq223181 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq222829 eq1091
    | exact resolve eq1091 eq222829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq222829
  have eq223312 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq412
       have i₂ := eq223181
       grind)
    | exact superpose eq223181 eq412
    | exact resolve eq412 eq223181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223356 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq223181
       grind)
    | exact superpose eq223181 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq223181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223395 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq223181
  have eq223396 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq223356
  have eq223397 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq223396
  have eq223437 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq223312
  have eq223445 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq223437
    | exact resolve eq223437 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223437
  have eq223622 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42468
       have i₂ := eq223397
       grind)
    | exact superpose eq223397 eq42468
    | exact resolve eq42468 eq223397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42468 eq223397
  have eq223693 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq223622
  have eq223715 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq223693
       have r₂ := eq223395
       grind)
    | exact resolve eq223693 eq223395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223693
  have eq223751 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq412
       have i₂ := eq223715
       grind)
    | exact superpose eq223715 eq412
    | exact resolve eq412 eq223715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223715
  have eq223843 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq223751
  have eq223881 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq223843
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq223843
    | exact resolve eq223843 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223843
  have eq224252 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq223881
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq223881
    | (have j1 := eq82 (σ x)
       grind)
    | exact resolve eq223881 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225444 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq223445
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq223445
    | (have j1 := eq82 (σ x)
       grind)
    | exact resolve eq223445 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223445
  have eq240246 : (k (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq222961
       grind)
    | exact superpose eq222961 eq45
    | exact resolve eq45 eq222961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222961
  have eq263100 : (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq223037
       have r₂ := eq223395
       grind)
    | exact resolve eq223037 eq223395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223037 eq223395
  have eq263482 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq88
       have i₂ := eq263100
       grind)
    | exact superpose eq263100 eq88
    | exact resolve eq88 eq263100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq263100
  have eq263528 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq263482
    | exact resolve eq263482 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263482
  have eq263543 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq263528
       have i₂ := eq82 sF3
       grind)
    | exact superpose eq82 eq263528
    | (have j1 := eq82 (σ y)
       grind)
    | exact resolve eq263528 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263950 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq240246
       have i₂ := eq222955
       grind)
    | exact superpose eq222955 eq240246
    | exact resolve eq240246 eq222955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222955 eq240246
  have eq264149 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq263950
  have eq264160 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq264149
    | exact resolve eq264149 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264149
  have eq264175 : (τ (σ (M.op x y))) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq264160 eq61
    | exact resolve eq61 eq264160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264274 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq264160 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq264160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264160
  have eq264370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq264274
    | exact resolve eq264274 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264274
  have eq264378 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq264175
    | exact resolve eq264175 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264175
  have eq264382 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq264370
       have r₂ := eq28
       grind)
    | exact resolve eq264370 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264370
  have eq264385 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq264382
    | exact resolve eq264382 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264382
  have eq265571 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq224252 eq633
    | exact resolve eq633 eq224252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq224252
  have eq265648 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq496 eq265571
    | (have j0 := eq265571 (σ x)
       grind)
    | exact resolve eq265571 eq496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496 eq265571
  have eq424125 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  have eq424167 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq34985
  have eq424863 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq35455 eq497
    | exact resolve eq497 eq35455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq35455
  have eq424904 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1423 eq424863
    | exact resolve eq424863 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423 eq424863
  have eq462781 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq424125 eq34700
    | exact resolve eq34700 eq424125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34700 eq424125
  have eq462813 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq462781
  have eq462829 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq462813
       have r₂ := eq424167
       grind)
    | exact resolve eq462813 eq424167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424167 eq462813
  have eq470548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq424904 eq462829
    | exact resolve eq462829 eq424904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424904 eq462829
  have eq470610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq470548
  have eq470644 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq470610
       have r₂ := eq28
       grind)
    | exact resolve eq470610 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470610
  have eq470661 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq470644
  have eq471290 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq470661 eq35404
    | exact resolve eq35404 eq470661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35404 eq470661
  have eq471383 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) := by grind
  clear eq471290
  have eq1868146 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq225444
  have eq1868191 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1868146
       have r₂ := eq471383
       grind)
    | exact resolve eq1868146 eq471383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471383 eq1868146
  have eq1868290 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1868191 eq53
    | exact resolve eq53 eq1868191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1868191
  have eq1907179 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  have eq1907248 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq263543
  have eq2021569 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1907179 eq263528
    | exact resolve eq263528 eq1907179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263528 eq1907179
  have eq2021620 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq2021569
  have eq2021654 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2021620
       have r₂ := eq1907248
       grind)
    | exact resolve eq2021620 eq1907248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907248 eq2021620
  have eq2021714 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2021654 eq357
    | exact resolve eq357 eq2021654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq2021654
  have eq2026116 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2021714 eq1868290
    | exact resolve eq1868290 eq2021714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868290 eq2021714
  have eq2026244 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq2026116
  have eq2026373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2026244 eq264385
    | exact resolve eq264385 eq2026244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264385 eq2026244
  have eq2026518 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2026373
  have eq2026557 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2026518
       have r₂ := eq28
       grind)
    | exact resolve eq2026518 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2026518
  have eq2026638 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2026557
  have eq2033641 : (τ (σ x)) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2026638 eq61
    | exact resolve eq61 eq2026638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2026638
  have eq2033962 : x = (k x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq2033641
    | exact resolve eq2033641 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033641
  have eq2033965 : y = (M.op x x) ∨ x = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2033962
       have r₂ := eq128877
       grind)
    | exact resolve eq2033962 eq128877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128877 eq2033962
  have eq2034040 : x = (k x y) ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq2033965
  have eq2034113 : x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq2034040
  have eq2034254 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq2034113
       grind)
    | exact superpose eq2034113 eq45
    | exact resolve eq45 eq2034113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq2034325 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq264378
       have i₂ := eq2034113
       grind)
    | exact superpose eq2034113 eq264378
    | exact resolve eq264378 eq2034113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264378 eq2034113
  have eq2034512 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2034325
  have eq2034633 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2034254
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2034254
    | exact resolve eq2034254 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034254
  have eq2038799 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2034633 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq2034633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2034633
  have eq2038944 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq2038799
    | exact resolve eq2038799 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038799
  have eq2038960 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq2038944
    | exact resolve eq2038944 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038944
  have eq2038987 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq632 X0 x
       have i₂ := eq2034512
       grind)
    | exact superpose eq2034512 eq632
    | exact resolve eq632 eq2034512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq2034512
  have eq2039228 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2038987 x
       have i₂ := eq495 sF0 x
       grind)
    | (have i₁ := eq2038987 x
       have i₂ := eq495 sF0 x
       grind)
    | exact superpose eq495 eq2038987
    | (have j0 := eq2038987 x
       grind)
    | exact resolve eq2038987 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq2038987
  have eq2039947 : x ≠ x ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2039228 eq12
    | exact resolve eq12 eq2039228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039228
  have eq2040016 : x ≠ x ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq2039947
  have eq2040017 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2040016
  have eq2040417 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2040017 eq5128
    | (have j0 := eq5128 (M.op x y) x
       grind)
    | exact resolve eq5128 eq2040017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5128
  have eq2040546 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2040417 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2040417
    | (have j0 := eq2040417 X0
       grind)
    | exact resolve eq2040417 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040417
  have eq2040612 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21 eq2040546
    | (have j0 := eq2040546 X0
       grind)
    | exact resolve eq2040546 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040546
  have eq2040653 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21 eq2040612
    | (have j0 := eq2040612 X0
       grind)
    | exact resolve eq2040612 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040612
  have eq2305856 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2038960 eq48
    | exact resolve eq48 eq2038960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq2305857 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2038960 eq51
    | exact resolve eq51 eq2038960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2038960
  have eq3414312 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2305857 eq2305856
    | exact resolve eq2305856 eq2305857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2305856 eq2305857
  have eq3414508 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq3414312
  have eq3414748 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3414508 eq416
    | exact resolve eq416 eq3414508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416
  have eq3414943 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3414748
  have eq3415032 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq3414943
    | exact resolve eq3414943 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3414943
  have eq3742245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq3414508 eq2040653
    | exact resolve eq2040653 eq3414508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040653 eq3414508
  have eq3742547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3742245
  have eq3742618 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq3742547
    | exact resolve eq3742547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3742547
  have eq3742653 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3742618
       have r₂ := eq28
       grind)
    | exact resolve eq3742618 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3742618
  have eq3742708 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3742653
  have eq3742844 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3742708 eq152
    | exact resolve eq152 eq3742708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq3742708
  have eq3743221 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq3742844
    | exact resolve eq3742844 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3742844
  have eq3743523 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3743221 eq2040017
    | exact resolve eq2040017 eq3743221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2040017 eq3743221
  have eq3743701 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3743523
  have eq3744044 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3743701 eq265648
    | exact resolve eq265648 eq3743701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265648 eq3743701
  have eq3744065 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3744044
  have eq3746061 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3744065
  have eq3746373 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3746061 eq223881
    | exact resolve eq223881 eq3746061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223881 eq3746061
  have eq3746626 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq3746373
  have eq3746783 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq3746626 eq30
    | exact resolve eq30 eq3746626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3746626
  have eq3747266 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3746783
    | exact resolve eq3746783 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3746783
  have eq3747267 : x = (M.op x y) ∨ x = y := by grind
  clear eq3747266
  have eq3747269 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3747267 eq21
    | exact resolve eq21 eq3747267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3747625 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3747267 eq42952
    | exact resolve eq42952 eq3747267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42952 eq3747267
  have eq3748065 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3747625
  have eq3748261 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq3747269
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3747269
    | exact resolve eq3747269 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3747269
  have eq3813496 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3748065
  have eq3816716 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3415032
       have i₂ := eq3813496
       grind)
    | exact superpose eq3813496 eq3415032
    | exact resolve eq3415032 eq3813496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3415032 eq3813496
  have eq3816872 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq3816716
  have eq3817123 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3816872 eq28
    | exact resolve eq28 eq3816872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816872
  have eq3817273 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq3817123
       have r₂ := eq3748261
       grind)
    | exact resolve eq3817123 eq3748261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748261 eq3817123
  have eq3817275 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq3817273 eq30
    | exact resolve eq30 eq3817273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3817273
  have eq3817770 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq3817275
    | exact resolve eq3817275 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3817275
  have eq3817771 : x = y := by grind
  clear eq3817770
  have eq3817773 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq3817771
       grind)
    | exact superpose eq3817771 eq19
    | exact resolve eq19 eq3817771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3817774 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq3817771
       grind)
    | exact superpose eq3817771 eq25
    | exact resolve eq25 eq3817771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq3817771
  have eq3818704 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3817774
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3817774
    | exact resolve eq3817774 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817774
  have eq3818706 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3818704 eq27
    | exact resolve eq27 eq3818704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq3818704
  have eq3819568 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq412
       have i₂ := eq3817773
       grind)
    | exact superpose eq3817773 eq412
    | exact resolve eq412 eq3817773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq3819695 : x = (k x (M.op x y)) := by grind
  clear eq3817773
  have eq3819834 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq3819568
    | exact resolve eq3819568 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819568
  have eq3820026 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  have eq3828122 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3819834 eq82
    | (have j0 := eq82 (σ x)
       grind)
    | exact resolve eq82 eq3819834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq3828242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3818706 eq3828122
    | exact resolve eq3828122 eq3818706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828122
  have eq3828274 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3828242
       have r₂ := eq28
       grind)
    | exact resolve eq3828242 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828242
  have eq3828279 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3818706 eq3828274
    | exact resolve eq3828274 eq3818706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828274
  have eq3828283 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3828279 eq28
    | exact resolve eq28 eq3828279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3828399 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3828279 eq3820026
    | exact resolve eq3820026 eq3828279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3820026 eq3828279
  have eq3829304 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3828399 eq3819834
    | exact resolve eq3819834 eq3828399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819834 eq3828399
  have eq3829379 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3829304
  have eq3829476 : x = (M.op x y) := by
    first
    | (have r₁ := eq3829379
       have r₂ := eq3828283
       grind)
    | exact resolve eq3829379 eq3828283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3828283 eq3829379
  have eq3829610 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3829476 eq21
    | exact resolve eq21 eq3829476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3830324 : x = (k x x) := by
    first
    | exact superpose eq3829476 eq3819695
    | exact resolve eq3819695 eq3829476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819695 eq3829476
  have eq3830533 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3829610
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3829610
    | exact resolve eq3829610 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3829610
  have eq3834060 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5145 x
       have i₂ := eq3830324
       grind)
    | exact superpose eq3830324 eq5145
    | (have j0 := eq5145 x
       grind)
    | exact resolve eq5145 eq3830324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5145 eq3830324
  have eq3834117 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq3834060
  have eq3834172 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3834117
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3834117
    | exact resolve eq3834117 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3834117
  have eq3834263 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3818706 eq3834172
    | exact resolve eq3834172 eq3818706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3818706 eq3834172
  have eq3834342 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3830533 eq3834263
    | exact resolve eq3834263 eq3830533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3830533 eq3834263
  have eq3834419 : False := by grind
  exact eq3834419

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyy_pyx_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq100 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X2 X1))) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
  have eq129 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X2 X1))) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq1409 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
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
  have eq1527 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1409 X1 X1 (M.op x (M.op x X0))
       have i₂ := eq129 X1 X0 x
       grind)
    | exact superpose eq129 eq1409
    | (have j1 := eq129 X1 X0 x
       grind)
    | exact resolve eq1409 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1409
  have eq1583 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1527 X0 X1
       have j1 := eq116 X0 X1
       grind)
    | (have r₁ := eq1527 X0 X1
       have r₂ := eq116 X0 X1
       grind)
    | (have r₁ := eq1527 X0 X0
       have r₂ := eq116 X0 X0
       grind)
    | exact resolve eq1527 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1527
  have eq1596 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1583 (σ X0) (σ X1)
       grind)
    | exact superpose eq1583 eq15
    | exact resolve eq15 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1615 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1596 X0 X1
       have i₂ := eq1583 X0 X1
       grind)
    | exact superpose eq1583 eq1596
    | exact resolve eq1596 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583 eq1596
  have eq1927 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1615 x y
       grind)
    | exact superpose eq1615 eq16
    | (have r₁ := eq16
       have r₂ := eq1615 x y
       grind)
    | exact resolve eq16 eq1615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615
  have eq1971 : False := by grind
  exact eq1971

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyx_pxy_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X0) X2 (M.op X0 X1)
       have i₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq36 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq19
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq48 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq48
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq84 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op X1 (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X1 (M.op X1 X0) (M.op X0 X2)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op (M.op (M.op X2 (M.op X2 (M.op X0 X1))) X3) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X2 (M.op X0 X1))) X3 X0
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (σ X0)
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq32
    | exact resolve eq32 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq86 (τ X0)
       grind)
    | exact superpose eq86 eq37
    | exact resolve eq37 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq104 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq86 (τ X0)
       grind)
    | exact superpose eq86 eq18
    | exact resolve eq18 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq105 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq104 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq104
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq103
    | exact resolve eq103 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq107 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq105
    | exact resolve eq105 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq107
    | exact resolve eq107 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq107
  have eq124 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op (M.op (M.op (M.op X0 X1) X0) X3) (M.op (M.op X0 X1) X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 (M.op (M.op (M.op X0 X1) X0) X3)
       have i₂ := eq26 X0 X1 X3
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq113 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq113
    | exact resolve eq113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) X1 (τ X0)
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61 y x
       grind)
    | exact superpose eq61 eq16
    | (have j1 := eq61 y x
       grind)
    | exact resolve eq16 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq438 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq36
    | exact resolve eq36 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq439 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq438 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq438
    | exact resolve eq438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq440 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    grind
  clear eq439
  have eq441 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (τ (M.op (σ X0) (σ X0))))) := by
    intro X0
    first
    | (have i₁ := eq440 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq440
    | exact resolve eq440 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ (M.op X0 X0)))
       have i₂ := eq440 X0
       grind)
    | exact superpose eq440 eq10
    | exact resolve eq10 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq475 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq441 X0
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq441
    | exact resolve eq441 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq481 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq475 X0
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq475
    | exact resolve eq475 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq803 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq219
       have i₂ := eq127 x
       grind)
    | exact superpose eq127 eq219
    | exact resolve eq219 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq804 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq803
       have i₂ := eq127 y
       grind)
    | exact superpose eq127 eq803
    | exact resolve eq803 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq805 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq804
       have i₂ := eq127 x
       grind)
    | exact superpose eq127 eq804
    | exact resolve eq804 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq807 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq805
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq805
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq805 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq808 : (σ y) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq807
  have eq875 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 X1))) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92 X0 X1 X3
       have i₂ := eq91 X1 X0 X2
       grind)
    | (have i₁ := eq92 (M.op X0 X2) X0 X2
       have i₂ := eq91 X0 (M.op X0 X2) X2
       grind)
    | exact superpose eq91 eq92
    | exact resolve eq92 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq891 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X0 (M.op X0 (M.op X1 (M.op X1 X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 (M.op X1 X2) X0
       have i₂ := eq92 X1 X2 X0
       grind)
    | (have i₁ := eq24 X0 (M.op X0 X1) X2
       have i₂ := eq92 X0 X1 X2
       grind)
    | exact superpose eq92 eq24
    | exact resolve eq24 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1836 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq451 X0
       grind)
    | exact superpose eq451 eq199
    | exact resolve eq199 eq451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq451
  have eq1932 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (τ (M.op (M.op (σ X0) (σ X0)) (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1836 (M.op (σ X0) (σ X0)) X1
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq1836
    | exact resolve eq1836 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1836
  have eq1976 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (M.op (σ X0) (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1932 X0 X1
       have i₂ := eq92 (σ X0) (σ X0) (M.op (σ X0) (σ X0))
       grind)
    | exact superpose eq92 eq1932
    | exact resolve eq1932 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932
  have eq1983 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1976 X0 X1
       have i₂ := eq9 (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq9 eq1976
    | exact resolve eq1976 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq1987 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1983 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1983
    | exact resolve eq1983 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq1992 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1987 (σ X0) X1
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq1987
    | exact resolve eq1987 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987
  have eq2225 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1992 X0 (σ (M.op X0 X0))
       have i₂ := eq127 (M.op X0 X0)
       grind)
    | exact superpose eq127 eq1992
    | exact resolve eq1992 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq4817 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) X1) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ X0) x
       have i₂ := eq2225 X0
       grind)
    | exact superpose eq2225 eq26
    | exact resolve eq26 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq4844 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) X1) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4817 X0 X1
       have i₂ := eq481 (M.op X0 X0)
       grind)
    | exact superpose eq481 eq4817
    | exact resolve eq4817 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4817
  have eq4867 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = (M.op (M.op (σ (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) X1) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4844 X1 X1
       have i₂ := eq92 X1 X1 (M.op X1 X1)
       grind)
    | exact superpose eq92 eq4844
    | exact resolve eq4844 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4844
  have eq4882 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq4867 x X1
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq4867
    | exact resolve eq4867 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4867
  have eq5382 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X0)) X1) (σ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq4882 (τ X0) X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq4882
    | exact resolve eq4882 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq4882
  have eq5436 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (σ (τ X0)) X1) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5382 X0 X1
       have i₂ := eq113 (M.op X0 X0)
       grind)
    | exact superpose eq113 eq5382
    | exact resolve eq5382 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq5382
  have eq5450 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5436 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5436
    | exact resolve eq5436 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5436
  have eq5753 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (M.op X0 X0) (M.op X0 X0) X1
       have i₂ := eq5450 X0 X0
       grind)
    | exact superpose eq5450 eq92
    | exact resolve eq92 eq5450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq5884 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 (M.op X0 X0) (M.op X0 X0) X1 x
       have i₂ := eq5753 X0 X1
       grind)
    | exact superpose eq5753 eq95
    | exact resolve eq95 eq5753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq5753
  have eq5981 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5884 X0 X1 X2
       have i₂ := eq5450 X1 X1
       grind)
    | exact superpose eq5450 eq5884
    | exact resolve eq5884 eq5450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5884
  have eq6109 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op (M.op X0 (M.op X1 X2)) X3) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X1 X2 (M.op (M.op X0 (M.op X1 X2)) X3)
       have i₂ := eq5981 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq5981 eq24
    | exact resolve eq24 eq5981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5981
  have eq6124 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op X1 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6109 X0 X1 X2 x
       have i₂ := eq91 (M.op X0 (M.op X1 X2)) X1 x
       grind)
    | exact superpose eq91 eq6109
    | exact resolve eq6109 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq6109
  have eq6273 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X0 X1))) = (M.op X0 (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6124 X0 X0 (M.op X2 (M.op X0 X1))
       have i₂ := eq6124 X2 X0 X1
       grind)
    | exact superpose eq6124 eq6124
    | exact resolve eq6124 eq6124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6124
  have eq12950 : (M.op x x) = (τ (σ y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq808
       grind)
    | exact superpose eq808 eq10
    | exact resolve eq10 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq13002 : y = (M.op x x) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12950
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq12950
    | exact resolve eq12950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12950
  have eq13003 : (σ (M.op x x)) = (σ (M.op y y)) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq13002
  have eq32620 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X1 X0))) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq891 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq5450 X0 X0
       grind)
    | exact superpose eq5450 eq891
    | exact resolve eq891 eq5450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq82503 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op (M.op X2 X2) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32620 X2 X0
       have i₂ := eq6273 X0 X2 X1
       grind)
    | (have i₁ := eq32620 X1 X2
       have i₂ := eq6273 X2 X1 X2
       grind)
    | exact superpose eq6273 eq32620
    | exact resolve eq32620 eq6273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6273 eq32620
  have eq723511 : (M.op y y) = (τ (σ (M.op x x))) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq13003
       grind)
    | exact superpose eq13003 eq10
    | exact resolve eq10 eq13003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13003
  have eq723921 : (M.op x x) = (M.op y y) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq723511
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq723511
    | exact resolve eq723511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723511
  have eq723922 : y = (M.op x x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq723921
  have eq723956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq481 x
       have i₂ := eq723922
       grind)
    | exact superpose eq723922 eq481
    | exact resolve eq481 eq723922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq723922
  have eq724582 : (M.op x x) = (M.op y y) := by
    first
    | (have r₁ := eq723956
       have r₂ := eq16
       grind)
    | exact resolve eq723956 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723956
  have eq727857 : ∀ X0 X1 : G, y = (M.op (M.op x x) (M.op (M.op (M.op (M.op y X0) y) X1) (M.op (M.op y X0) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq124 y X0 y X1
       have i₂ := eq724582
       grind)
    | exact superpose eq724582 eq124
    | exact resolve eq124 eq724582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq728167 : ∀ X0 X1 : G, y = (M.op (M.op x x) (M.op (M.op x x) (M.op (M.op (M.op (M.op y X0) y) X1) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq727857 X0 X1
       have i₂ := eq875 (M.op (M.op (M.op y X0) y) X1) y X0 (M.op x x)
       grind)
    | exact superpose eq875 eq727857
    | exact resolve eq727857 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727857
  have eq728204 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op x x) (M.op (M.op y X0) y))) := by
    intro X0
    first
    | (have i₁ := eq728167 X0 x
       have i₂ := eq26 y X0 x
       grind)
    | exact superpose eq26 eq728167
    | exact resolve eq728167 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq728167
  have eq728211 : y = (M.op (M.op x x) (M.op (M.op x x) (M.op (M.op x x) y))) := by
    first
    | (have i₁ := eq728204 x
       have i₂ := eq875 (M.op x x) y x (M.op x x)
       grind)
    | exact superpose eq875 eq728204
    | exact resolve eq728204 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq728204
  have eq728212 : y = (M.op (M.op x x) (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq728211
       have i₂ := eq82503 (M.op x x) (M.op x x) y
       grind)
    | exact superpose eq82503 eq728211
    | exact resolve eq728211 eq82503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82503 eq728211
  have eq728213 : y = (M.op (M.op x x) (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq728212
       have i₂ := eq724582
       grind)
    | exact superpose eq724582 eq728212
    | exact resolve eq728212 eq724582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724582 eq728212
  have eq728214 : x = y := by
    first
    | (have i₁ := eq728213
       have i₂ := eq5450 x x
       grind)
    | exact superpose eq5450 eq728213
    | exact resolve eq728213 eq5450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5450 eq728213
  have eq731944 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq728214
       grind)
    | exact superpose eq728214 eq16
    | exact resolve eq16 eq728214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728214
  have eq731945 : False := by grind
  exact eq731945

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxx_pyx_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq41 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq23
  have eq66 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq73 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq106 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq24 X0 X1 X2
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 (M.op X0 X1)) X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X1)) X2 X0
       have i₂ := eq24 X0 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq115 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq75 (σ X1) (σ X0)
       grind)
    | exact superpose eq75 eq15
    | (have j1 := eq75 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq331 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq66 X1 X0
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq66 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq66 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq66 X0 X1
       grind)
    | exact resolve eq13 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq369 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq331 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq370 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq369 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq375 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq370 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq370
    | (have j0 := eq370 X0 X1
       grind)
    | exact resolve eq370 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq568 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq106 X2 X0 (M.op X0 X1)
       grind)
    | (have i₁ := eq9 X1 X1 (M.op X1 X1)
       have i₂ := eq106 (M.op X1 X1) X1 (M.op X1 X1)
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x)
       have i₂ := eq568 X0 x X1
       grind)
    | exact superpose eq568 eq9
    | exact resolve eq9 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op X0 X1) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq108 (M.op X0 X1) (M.op X2 X0) X2
       have i₂ := eq568 X0 X1 X2
       grind)
    | exact superpose eq568 eq108
    | exact resolve eq108 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq568
  have eq1294 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ X0) (σ X1)) (M.op X2 (M.op X2 (σ X1)))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq115 X0 X1
       grind)
    | (have i₁ := eq9 (σ X0) (σ X1) X2
       have i₂ := eq115 X0 X1
       grind)
    | exact superpose eq115 eq9
    | (have j1 := eq115 X0 X1
       grind)
    | exact resolve eq9 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq2739 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq375 (τ X1) (τ X0)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq375
    | (have j0 := eq375 (τ (k X0 X1)) (τ X0)
       grind)
    | exact resolve eq375 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq3073 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2739 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2739
    | (have j0 := eq2739 X0 X1
       grind)
    | exact resolve eq2739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2739
  have eq3097 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3073 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3073
    | (have j0 := eq3073 X0 X1
       grind)
    | exact resolve eq3073 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073
  have eq3107 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3097 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3097
    | (have j0 := eq3097 X0 X1
       grind)
    | exact resolve eq3097 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3097
  have eq3115 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3107 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3107
    | (have j0 := eq3107 X0 X1
       grind)
    | exact resolve eq3107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107
  have eq3120 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3115 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3115
    | (have j0 := eq3115 X0 X1
       grind)
    | exact resolve eq3115 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3115
  have eq3125 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3120 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3120
    | (have j0 := eq3120 X0 X1
       grind)
    | exact resolve eq3120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3120
  have eq3130 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3125 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3125
    | (have j0 := eq3125 X0 X1
       grind)
    | exact resolve eq3125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3125
  have eq40491 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  clear eq3130
  have eq41182 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40491 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40491
  have eq42109 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41182 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42110 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41182 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41182
  have eq42592 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42109 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42109
  have eq42785 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq42592 (σ X0)
       grind)
    | exact superpose eq42592 eq15
    | exact resolve eq15 eq42592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42792 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq42592 (τ X0)
       grind)
    | exact superpose eq42592 eq37
    | exact resolve eq37 eq42592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq42823 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq42792 X0
       have i₂ := eq42592 X0
       grind)
    | exact superpose eq42592 eq42792
    | exact resolve eq42792 eq42592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42792
  have eq42830 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq42785 X0
       have i₂ := eq42592 X0
       grind)
    | exact superpose eq42592 eq42785
    | exact resolve eq42785 eq42592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42592 eq42785
  have eq44619 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq855 (τ X0) (τ X0) x
       have i₂ := eq42823 X0
       grind)
    | exact superpose eq42823 eq855
    | exact resolve eq855 eq42823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq49689 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (τ (M.op X0 X0)) ∨ (τ (M.op X0 X0)) = (k (τ X0) (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42110 (τ X0) (M.op (τ (M.op X0 X0)) X1)
       have i₂ := eq44619 X0 X1
       grind)
    | exact superpose eq44619 eq42110
    | exact resolve eq42110 eq44619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42110 eq44619
  have eq49690 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k (τ X0) (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq49689 X0 X1
       grind)
    | (have r₁ := eq49689 X0 X1
       have r₂ := eq42823 X0
       grind)
    | exact resolve eq49689 eq42823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42823 eq49689
  have eq56841 : ∀ X0 X1 : G, (τ (M.op (M.op (σ X0) (M.op (σ X0) (σ X0))) (M.op (σ X0) (M.op (σ X0) (σ X0))))) = (k (k (τ (M.op (σ X0) (σ X0))) X0) (M.op (τ (M.op (M.op (σ X0) (M.op (σ X0) (σ X0))) (M.op (σ X0) (M.op (σ X0) (σ X0))))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq49690 (M.op (σ X0) (M.op (σ X0) (σ X0))) X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq49690
    | exact resolve eq49690 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq49690
  have eq57007 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k (τ (M.op (σ X0) (σ X0))) X0) (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56841 X0 X1
       have i₂ := eq9 (σ X0) (M.op (σ X0) (σ X0)) (σ X0)
       grind)
    | exact superpose eq9 eq56841
    | exact resolve eq56841 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56841
  have eq57024 : ∀ X0 X1 : G, (k (k (τ (M.op (σ X0) (σ X0))) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57007 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq57007
    | exact resolve eq57007 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57007
  have eq57031 : ∀ X0 X1 : G, (k (k (τ (σ (M.op X0 X0))) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57024 X0 X1
       have i₂ := eq42830 X0
       grind)
    | exact superpose eq42830 eq57024
    | exact resolve eq57024 eq42830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42830 eq57024
  have eq57036 : ∀ X0 X1 : G, (k (k (M.op X0 X0) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57031 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq57031
    | exact resolve eq57031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57031
  have eq57039 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) (M.op X0 X1)) = X0 := by
    intro X0 X1
    grind
  clear eq57036
  have eq58270 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57039 (M.op X0 X1) (M.op (M.op X0 x) (M.op x X0))
       have i₂ := eq861 X0 x x X1
       grind)
    | exact superpose eq861 eq57039
    | exact resolve eq57039 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq57039
  have eq58419 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq58270 X0 X1
       have i₂ := eq106 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq106 eq58270
    | exact resolve eq58270 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq58270
  have eq92081 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58419 (σ X1) (σ X0)
       have i₂ := eq1294 X1 X0 (σ X1)
       grind)
    | exact superpose eq1294 eq58419
    | (have j1 := eq1294 X1 X0 x
       grind)
    | exact resolve eq58419 eq1294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294 eq58419
  have eq92394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92081 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq92081
    | (have j0 := eq92081 X0 X1
       grind)
    | exact resolve eq92081 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92081
  have eq92395 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq92394 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92394
  have eq92517 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92395 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92395
    | exact resolve eq92395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92644 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92395 y x
       grind)
    | exact superpose eq92395 eq16
    | exact resolve eq16 eq92395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92395
  have eq95767 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq92517 X0 (τ X1)
       grind)
    | exact superpose eq92517 eq18
    | exact resolve eq18 eq92517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq92517
  have eq95971 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq95767 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq95767
    | exact resolve eq95767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95767
  have eq96073 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95971 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95971
    | exact resolve eq95971 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95971
  have eq97728 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq92644
       have i₂ := eq96073 x y
       grind)
    | exact superpose eq96073 eq92644
    | exact resolve eq92644 eq96073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92644 eq96073
  have eq97729 : False := by grind
  exact eq97729

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation1469 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1469 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  clear eq22
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
  have eq76 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq94 x y
       grind)
    | exact superpose eq94 eq44
    | (have j1 := eq94 x y
       grind)
    | exact resolve eq44 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq120 eq94
    | (have j0 := eq94 (σ x) (σ y)
       grind)
    | exact resolve eq94 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq124
       have r₂ := eq27
       grind)
    | exact resolve eq124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq27
    | exact resolve eq27 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq77
    | (have r₁ := eq77
       have r₂ := eq129
       grind)
    | exact resolve eq77 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq129
  have eq592 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq591
  have eq1233 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq592 eq120
    | exact resolve eq120 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq1237 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1233
  have eq1242 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1237
       have r₂ := eq131
       grind)
    | exact resolve eq1237 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq1237
  have eq1268 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1242 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1242
       grind)
    | exact resolve eq13 eq1242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1275 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1275 eq120
    | exact resolve eq120 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1275
  have eq1479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1475
  have eq1484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1479
    | exact resolve eq1479 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479
  have eq1486 : y = (M.op x y) := by
    first
    | (have r₁ := eq1484
       have r₂ := eq27
       grind)
    | exact resolve eq1484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1488 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1486 eq20
    | exact resolve eq20 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1493 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq1486 eq76
    | (have r₁ := eq76
       have r₂ := eq1486
       grind)
    | exact resolve eq76 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq1486
  have eq1497 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq1493
  have eq1504 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1488
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1488
    | exact resolve eq1488 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1507 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1504 eq26
    | exact resolve eq26 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1829 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1497
       grind)
    | exact superpose eq1497 eq44
    | exact resolve eq44 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1836 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1504 eq1829
    | exact resolve eq1829 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq1838 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1836
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1836
    | exact resolve eq1836 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1836
  have eq1839 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1504 eq1838
    | exact resolve eq1838 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq1843 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1839 eq94
    | (have j0 := eq94 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq94 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839
  have eq1844 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by grind
  clear eq1843
  have eq1846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1507 eq1844
    | exact resolve eq1844 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq1849 : y = (M.op y y) := by
    first
    | (have r₁ := eq1846
       have r₂ := eq27
       grind)
    | exact resolve eq1846 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846
  have eq1861 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1849
       grind)
    | exact superpose eq1849 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1849
       grind)
    | exact resolve eq13 eq1849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849
  have eq1869 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1861 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq1889 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1869 x
       grind)
    | exact superpose eq1869 eq44
    | exact resolve eq44 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1869
  have eq1896 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1504 eq1889
    | exact resolve eq1889 eq1504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504 eq1889
  have eq1900 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1896
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1896
    | exact resolve eq1896 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1896
  have eq1903 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1900
    | exact resolve eq1900 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1900
  have eq1970 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1903 eq94
    | (have j0 := eq94 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq94 eq1903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1903
  have eq1971 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq1970
  have eq1973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1507 eq1971
    | exact resolve eq1971 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507 eq1971
  have eq1976 : False := by grind
  exact eq1976

/-- `Equation1469`: `x = (x ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_x_pyx_Equation1469 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1469 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1469.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X2 X0))) = X0 := by
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
  have eq53 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X0 (M.op X3 (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 (M.op X0 X1) (M.op x (M.op x X0)) X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op x (M.op x y))) := by
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
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq92 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq92
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq106
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq106
    | exact resolve eq106 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq218 : ∀ X1 : G, (M.op x y) = (M.op x (M.op X1 (M.op X1 (M.op x y)))) := by
    intro X1
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X1 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 (M.op X2 (M.op X0 X1)) X0
       have i₂ := eq55 X0 X1 X2
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op x y))) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq218 eq55
    | exact resolve eq55 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq561 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq221 eq55
    | exact resolve eq55 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq221
  have eq4639 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x y) (M.op X0 x))) := by
    intro X0
    first
    | exact superpose eq53 eq555
    | exact resolve eq555 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq4643 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x)))) := by
    intro X0
    first
    | exact superpose eq54 eq555
    | exact resolve eq555 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq555
  have eq13258 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq107 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq13258
    | exact resolve eq13258 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13258
  have eq13270 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq13259
       have r₂ := eq28
       grind)
    | exact resolve eq13259 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13259
  have eq13274 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq13270
    | exact resolve eq13270 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13270
  have eq13289 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13274 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13274
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq13274
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13274
       grind)
    | exact resolve eq12 eq13274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13274
  have eq13311 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq13289
  have eq13315 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq13311
       have r₂ := eq27
       grind)
    | exact resolve eq13311 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13311
  have eq13572 : (τ (σ y)) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13315 eq104
    | exact resolve eq104 eq13315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq13573 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq13315 eq107
    | exact resolve eq107 eq13315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq13315
  have eq13582 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq13573
  have eq13592 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | exact superpose eq30 eq13572
    | exact resolve eq13572 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13572
  have eq13604 : y = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq13582
       grind)
    | exact superpose eq13582 eq56
    | exact resolve eq56 eq13582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq13608 : x = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4639 y
       have i₂ := eq13582
       grind)
    | exact superpose eq13582 eq4639
    | exact resolve eq4639 eq13582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639 eq13582
  have eq13640 : x = (M.op (M.op x y) (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq559 eq13608
    | exact resolve eq13608 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq13608
  have eq14087 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq13592
       grind)
    | exact superpose eq13592 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13592
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13592
       grind)
    | exact resolve eq12 eq13592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13592
  have eq14109 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq14087
  have eq14112 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14109
       have r₂ := eq19
       grind)
    | exact resolve eq14109 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14109
  have eq14118 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq14112
       grind)
    | exact superpose eq14112 eq92
    | exact resolve eq92 eq14112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq14112
  have eq14135 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14118
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14118
    | exact resolve eq14118 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14118
  have eq14168 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14135 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq14135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14135
  have eq14169 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14168
  have eq14173 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq14169
    | exact resolve eq14169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14169
  have eq14184 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq14173
    | exact resolve eq14173 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14173
  have eq15315 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13640 eq13604
    | exact resolve eq13604 eq13640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13604 eq13640
  have eq15349 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq15315
  have eq15354 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq15349 eq30
    | exact resolve eq30 eq15349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15349
  have eq15472 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq15354
    | exact resolve eq15354 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15354
  have eq15473 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq15472
  have eq15517 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq15473 eq30
    | exact resolve eq30 eq15473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq15520 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq15473 eq57
    | exact resolve eq57 eq15473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq15597 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15473 eq14184
    | exact resolve eq14184 eq15473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14184 eq15473
  have eq15598 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq15597
  have eq15618 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq15598
       have r₂ := eq28
       grind)
    | exact resolve eq15598 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15598
  have eq15669 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq15517
    | exact resolve eq15517 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15517
  have eq21631 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq15618 eq4643
    | exact resolve eq4643 eq15618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4643
  have eq21664 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq561 eq21631
    | exact resolve eq21631 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq21631
  have eq24344 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq15618 eq15520
    | exact resolve eq15520 eq15618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15520 eq15618
  have eq24411 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq24344
  have eq55992 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq24411 eq21664
    | exact resolve eq21664 eq24411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21664 eq24411
  have eq56066 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq55992
  have eq56076 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq56066 eq29
    | exact resolve eq29 eq56066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq56066
  have eq56299 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq56076
    | exact resolve eq56076 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq56076
  have eq56436 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq56299 eq15669
    | exact resolve eq15669 eq56299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15669 eq56299
  have eq56577 : x = y := by grind
  clear eq56436
  have eq56682 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq56577
       grind)
    | exact superpose eq56577 eq19
    | exact resolve eq19 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq56683 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq56577
       grind)
    | exact superpose eq56577 eq25
    | exact resolve eq25 eq56577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq56577
  have eq56819 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq56683
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq56683
    | exact resolve eq56683 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq56683
  have eq56839 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq56819 eq27
    | exact resolve eq27 eq56819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq56819
  have eq57203 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq56839 eq71
    | exact resolve eq71 eq56839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq56839
  have eq57299 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq57203
       have i₂ := eq56682
       grind)
    | exact superpose eq56682 eq57203
    | exact resolve eq57203 eq56682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56682 eq57203
  have eq57731 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57299 eq15
    | exact resolve eq15 eq57299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57299
  have eq57807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq57731
    | exact resolve eq57731 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq57731
  have eq57828 : False := by grind
  exact eq57828

/-- `Equation1473`: `x = (x ◇ y) ◇ (z ◇ (w ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pxy_pyx_pyy_pyx_Equation1473 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1473 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1473.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 (M.op X3 X0))) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 X1 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op X4 (M.op X5 (M.op X0 X1)))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op x (M.op x X0)) X4 X5
       have i₂ := eq9 X0 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 x) x
       have i₂ := eq9 X0 x x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X2) ≠ X0 ∨ (k (M.op X0 (M.op X1 X0)) X2) = (M.op X2 X2) ∨ (M.op X2 (M.op X0 (M.op X1 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X1 X0)) X2
       have i₂ := eq9 X0 (M.op X1 X0) X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op X0 (M.op X1 X0)) X2
       grind)
    | exact resolve eq13 eq9
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
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq58 (τ X0)
       grind)
    | exact superpose eq58 eq18
    | exact resolve eq18 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq66 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq66
    | exact resolve eq66 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq66
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq69 X1
       grind)
    | exact superpose eq69 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq89
  have eq156 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq19 X1 (M.op X2 X0) X3 (M.op X0 x)
       have i₂ := eq9 X0 x X1 X2
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq19 X3 X2 X4 X0
       have i₂ := eq156 X2 X0 X3 X1
       grind)
    | (have i₁ := eq19 X3 X2 X4 X0
       have i₂ := eq156 X2 X0 X1 X3
       grind)
    | exact superpose eq156 eq19
    | exact resolve eq19 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq156
  have eq381 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X2 (M.op X3 (M.op X4 X1))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq12 (M.op X4 (M.op X0 (M.op X1 X2))) X3
       have i₂ := eq210 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq210 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq524 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq494 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq494
    | (have j0 := eq494 X0 X1
       grind)
    | exact resolve eq494 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq494
  have eq529 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq524 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq524 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq524 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq534 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq529
    | (have j0 := eq529 X0 X1
       grind)
    | exact resolve eq529 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq529
  have eq701 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) X1) ∨ (M.op X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op X0 X1) X2 X1
       have i₂ := eq21 X1 X0 (M.op X2 (M.op X0 X1))
       grind)
    | exact superpose eq21 eq56
    | (have j0 := eq56 (M.op X0 X1) X2 X1
       grind)
    | (have r₁ := eq56 (M.op X1 X0) X1 X0
       have r₂ := eq21 X0 X1 (M.op X1 (M.op X1 X0))
       grind)
    | exact resolve eq56 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq56
  have eq710 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) X1) ∨ (M.op X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq701 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq718 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq710 X0 X1 X2
       have i₂ := eq210 X2 X0 X1 X1 (M.op X0 X1)
       grind)
    | exact superpose eq210 eq710
    | (have j0 := eq710 X0 X1 X2
       grind)
    | exact resolve eq710 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq728 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1))) X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq718 X0 X1 X2
       have j1 := eq381 X1 X1 (M.op X0 X1) X2 X0
       grind)
    | (have r₁ := eq718 X0 X1 X2
       have r₂ := eq381 X1 X1 X2 x x
       grind)
    | exact resolve eq718 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq718
  have eq2527 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq534
    | exact resolve eq534 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq2789 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k (M.op (M.op X0 X0) (M.op X2 (M.op X0 X0))) X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq728 X1 X0 X2
       have i₂ := eq2527 X0 X1
       grind)
    | (have i₁ := eq728 X1 X1 X2
       have i₂ := eq2527 X0 X1
       grind)
    | exact superpose eq2527 eq728
    | (have j1 := eq2527 X1 X0
       grind)
    | exact resolve eq728 eq2527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq2893 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X0) = (M.op X2 (M.op X3 (M.op X4 (M.op X0 X1)))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq210 X4 X0 X0 X2 X3
       have i₂ := eq2527 X1 X0
       grind)
    | (have i₁ := eq210 X0 X1 X0 X3 X4
       have i₂ := eq2527 X0 X1
       grind)
    | exact superpose eq2527 eq210
    | (have j1 := eq2527 X1 X0
       grind)
    | exact resolve eq210 eq2527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq2954 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X2 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2893 X0 X1 X2 x x
       have i₂ := eq210 x X0 X1 X2 x
       grind)
    | exact superpose eq210 eq2893
    | (have j0 := eq2893 X0 X1 X2 x x
       grind)
    | exact resolve eq2893 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq2893
  have eq2969 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2789 X0 X1 x
       have i₂ := eq9 X0 X0 x X0
       grind)
    | exact superpose eq9 eq2789
    | (have j0 := eq2789 X0 X1 x
       grind)
    | exact resolve eq2789 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789
  have eq3456 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2969 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2969
  have eq3458 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3456 X0 X1
       have j1 := eq2954 X0 X1 x
       grind)
    | (have r₁ := eq3456 X0 X1
       have r₂ := eq2954 X0 X1 X1
       grind)
    | (have r₁ := eq3456 X1 X0
       have r₂ := eq2954 X0 X1 X0
       grind)
    | exact resolve eq3456 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954 eq3456
  have eq3563 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3458 (σ X1) (σ X0)
       grind)
    | exact superpose eq3458 eq15
    | exact resolve eq15 eq3458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3582 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3563 X0 X1
       have i₂ := eq3458 X1 X0
       grind)
    | exact superpose eq3458 eq3563
    | exact resolve eq3563 eq3458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3458 eq3563
  have eq4507 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3582 x y
       grind)
    | exact superpose eq3582 eq16
    | (have r₁ := eq16
       have r₂ := eq3582 x y
       grind)
    | exact resolve eq16 eq3582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3582
  have eq4569 : False := by grind
  exact eq4569
