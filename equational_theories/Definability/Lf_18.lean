import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 (M.op X0 X0) X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq51 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq51 (σ X1) (σ X0)
       grind)
    | exact superpose eq51 eq13
    | (have j1 := eq51 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq51 X1 (τ X0)
       grind)
    | exact superpose eq51 eq15
    | (have j1 := eq51 X1 (τ X0)
       grind)
    | exact resolve eq15 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq51
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (σ X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 X1 (σ X0)
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq72 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq72
    | exact resolve eq72 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq437 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq399
    | (have j0 := eq399 X0 X1
       grind)
    | exact resolve eq399 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq599 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq14
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq14 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq599
       have i₂ := eq437 x y
       grind)
    | exact superpose eq437 eq599
    | (have j1 := eq437 (σ x) (σ y)
       grind)
    | (have r₁ := eq599
       have r₂ := eq437 x y
       grind)
    | exact resolve eq599 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq2160 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2159
  have eq2164 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2160
       grind)
    | exact superpose eq2160 eq14
    | exact resolve eq14 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2167 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ x) (σ y)
       have i₂ := eq2160
       grind)
    | exact superpose eq2160 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | (have r₁ := eq11 (σ x) (σ y)
       have r₂ := eq2160
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq2160
       grind)
    | exact resolve eq11 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2169 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2167
  have eq2171 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2169
       have i₂ := eq26 y
       grind)
    | exact superpose eq26 eq2169
    | exact resolve eq2169 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2169
  have eq2174 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2171
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq2171
    | exact resolve eq2171 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq41194 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq81 y (σ x)
       have i₂ := eq2174
       grind)
    | exact superpose eq2174 eq81
    | (have j0 := eq81 y (σ x)
       grind)
    | (have r₁ := eq81 y (σ x)
       have r₂ := eq2174
       grind)
    | exact resolve eq81 eq2174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2174
  have eq41201 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq41194
  have eq41208 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41201
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq41201
    | exact resolve eq41201 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41201
  have eq68950 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2160
       have i₂ := eq41208
       grind)
    | exact superpose eq41208 eq2160
    | exact resolve eq2160 eq41208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160 eq41208
  have eq68959 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq68950
  have eq70017 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq437 x y
       have i₂ := eq68959
       grind)
    | exact superpose eq68959 eq437
    | (have j0 := eq437 x y
       grind)
    | exact resolve eq437 eq68959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq68959
  have eq70097 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq70017
  have eq70122 : y = (M.op x y) := by
    first
    | (have r₁ := eq70097
       have r₂ := eq2164
       grind)
    | exact resolve eq70097 eq2164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2164 eq70097
  have eq71455 : y ≠ y ∨ (M.op y y) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq70122
       grind)
    | exact superpose eq70122 eq11
    | (have j0 := eq11 x y
       grind)
    | (have r₁ := eq11 x y
       have r₂ := eq70122
       grind)
    | exact resolve eq11 eq70122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71458 : y = (k x y) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq71455
  have eq73270 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq610 x y
       have i₂ := eq71458
       grind)
    | exact superpose eq71458 eq610
    | (have j0 := eq610 x y
       grind)
    | exact resolve eq610 eq71458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71458
  have eq73339 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq73270
  have eq74719 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq73339
       grind)
    | exact superpose eq73339 eq14
    | exact resolve eq14 eq73339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73339
  have eq74729 : (σ y) ≠ (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq74719
       have i₂ := eq70122
       grind)
    | exact superpose eq70122 eq74719
    | exact resolve eq74719 eq70122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74719
  have eq74730 : (M.op y y) = (M.op y x) := by grind
  clear eq74729
  have eq75789 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq74730
       grind)
    | exact superpose eq74730 eq10
    | (have j0 := eq10 X0 y
       grind)
    | (have r₁ := eq10 x y
       have r₂ := eq74730
       grind)
    | exact resolve eq10 eq74730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74730
  have eq76163 : (M.op x y) = (k x y) := by
    first
    | (have j0 := eq75789 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75789
  have eq76165 : y = (k x y) := by
    first
    | (have i₁ := eq76163
       have i₂ := eq70122
       grind)
    | exact superpose eq70122 eq76163
    | exact resolve eq76163 eq70122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76163
  have eq77250 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq610 x y
       have i₂ := eq76165
       grind)
    | exact superpose eq76165 eq610
    | (have j0 := eq610 x y
       grind)
    | exact resolve eq610 eq76165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq76165
  have eq77320 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq77250
  have eq78723 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq77320
       grind)
    | exact superpose eq77320 eq14
    | exact resolve eq14 eq77320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77320
  have eq78733 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq78723
       have i₂ := eq70122
       grind)
    | exact superpose eq70122 eq78723
    | exact resolve eq78723 eq70122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70122 eq78723
  have eq78734 : False := by grind
  exact eq78734

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_pyx_x_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq12 X2 X0
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X2 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X2 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X2 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X2 X2
       have j1 := eq47 X0 X2 X2
       grind)
    | (have r₁ := eq41 X0 X1 X2
       have r₂ := eq47 X0 X1 X2
       grind)
    | (have r₁ := eq41 X0 X2 X1
       have r₂ := eq47 X0 X1 X2
       grind)
    | (have r₁ := eq41 X0 X1 (M.op X0 X2)
       have r₂ := eq47 X0 (M.op X0 X2) X2
       grind)
    | exact resolve eq41 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq47
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq50
    | (have j0 := eq50 (σ X1) (σ X0)
       grind)
    | exact resolve eq50 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq112 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq143 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq144 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq145 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq144 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq271 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq273 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       have j1 := eq112 X1 X0
       grind)
    | (have r₁ := eq271 X1 X0
       have r₂ := eq112 X0 X1
       grind)
    | exact resolve eq271 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq271
  have eq338 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq145 X1 (τ X0)
       grind)
    | exact superpose eq145 eq16
    | (have j1 := eq145 X1 (τ X0)
       grind)
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq145
  have eq639 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq273 x y
       grind)
    | exact superpose eq273 eq14
    | (have j1 := eq273 x y
       grind)
    | exact resolve eq14 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq273 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq2358 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq338 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq338
    | exact resolve eq338 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq2447 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2358 X0 X1
       have i₂ := eq13 X1 X0
       grind)
    | exact superpose eq13 eq2358
    | (have j0 := eq2358 X0 X1
       grind)
    | exact resolve eq2358 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358
  have eq3295 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq639
       have i₂ := eq2447 x y
       grind)
    | exact superpose eq2447 eq639
    | (have j1 := eq2447 (σ x) (σ y)
       grind)
    | (have r₁ := eq639
       have r₂ := eq2447 x y
       grind)
    | exact resolve eq639 eq2447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq3296 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3295
  have eq3620 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq3296
       grind)
    | exact superpose eq3296 eq14
    | exact resolve eq14 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3621 : (σ y) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq3296
       grind)
    | exact superpose eq3296 eq10
    | exact resolve eq10 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3622 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq3296
       grind)
    | exact superpose eq3296 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq3296
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq3296
       grind)
    | exact resolve eq11 eq3296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq3625 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3622
  have eq3626 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3625
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq3625
    | exact resolve eq3625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625
  have eq3627 : (σ y) ≠ (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3621
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq3621
    | exact resolve eq3621 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3621
  have eq3630 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3626
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq3626
    | exact resolve eq3626 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3626
  have eq3631 : (σ y) = (σ (k y x)) ∨ (σ y) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3627
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq3627
    | exact resolve eq3627 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3627
  have eq3632 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3631
       have r₂ := eq3630
       grind)
    | exact resolve eq3631 eq3630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3630 eq3631
  have eq4255 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2447 x y
       have i₂ := eq3632
       grind)
    | exact superpose eq3632 eq2447
    | (have j0 := eq2447 x y
       grind)
    | exact resolve eq2447 eq3632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447 eq3632
  have eq4307 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq4255
  have eq4332 : y = (M.op x y) := by
    first
    | (have r₁ := eq4307
       have r₂ := eq3620
       grind)
    | exact resolve eq4307 eq3620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3620 eq4307
  have eq4639 : y ≠ (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq4332
       grind)
    | exact superpose eq4332 eq10
    | exact resolve eq10 eq4332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4640 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq4332
       grind)
    | exact superpose eq4332 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq4332
       grind)
    | exact resolve eq11 eq4332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4642 : y = (M.op x x) ∨ y = (k y x) := by grind
  clear eq4640
  have eq4643 : y = (k y x) := by
    first
    | (have r₁ := eq4639
       have r₂ := eq4642
       grind)
    | exact resolve eq4639 eq4642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639 eq4642
  have eq5039 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq655 x y
       have i₂ := eq4643
       grind)
    | exact superpose eq4643 eq655
    | (have j0 := eq655 x y
       grind)
    | exact resolve eq655 eq4643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq4643
  have eq5046 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5039
  have eq6102 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq5046
       grind)
    | exact superpose eq5046 eq14
    | exact resolve eq14 eq5046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5046
  have eq6110 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6102
       have i₂ := eq4332
       grind)
    | exact superpose eq4332 eq6102
    | exact resolve eq6102 eq4332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4332 eq6102
  have eq6111 : False := by grind
  exact eq6111

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_y_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq15 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq21 (σ X0)
       grind)
    | exact superpose eq21 eq13
    | exact resolve eq13 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq23
    | exact resolve eq23 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq23
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq12 X2 X0
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X2 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X2 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq41 X0 X2 X2
       have j1 := eq47 X0 X2 X2
       grind)
    | (have r₁ := eq41 X0 X1 X2
       have r₂ := eq47 X0 X1 X2
       grind)
    | (have r₁ := eq41 X0 X2 X1
       have r₂ := eq47 X0 X1 X2
       grind)
    | exact resolve eq41 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq47
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq50
    | (have j0 := eq50 (σ X1) (σ X0)
       grind)
    | exact resolve eq50 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq141 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq142 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq143 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq142 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq270 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq274 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq270 X0 X1
       have j1 := eq110 X1 X0
       grind)
    | (have r₁ := eq270 X1 X0
       have r₂ := eq110 X0 X1
       grind)
    | exact resolve eq270 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq270
  have eq321 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq143 (τ X1) X0
       grind)
    | exact superpose eq143 eq15
    | (have j1 := eq143 (τ X1) X0
       grind)
    | exact resolve eq15 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15 eq143
  have eq597 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq274 x y
       grind)
    | exact superpose eq274 eq14
    | (have j1 := eq274 x y
       grind)
    | exact resolve eq14 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq2134 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq321 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq321
    | exact resolve eq321 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq2220 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2134 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq2134
    | (have j0 := eq2134 X0 X1
       grind)
    | exact resolve eq2134 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134
  have eq2865 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq597
       have i₂ := eq2220 y x
       grind)
    | exact superpose eq2220 eq597
    | (have j1 := eq2220 (σ y) (σ x)
       grind)
    | (have r₁ := eq597
       have r₂ := eq2220 y x
       grind)
    | exact resolve eq597 eq2220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq2866 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2865
  have eq3051 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq2866
       grind)
    | exact superpose eq2866 eq14
    | exact resolve eq14 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3052 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (σ y) (σ x)
       have i₂ := eq2866
       grind)
    | exact superpose eq2866 eq10
    | exact resolve eq10 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3053 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 (σ y) (σ x)
       have i₂ := eq2866
       grind)
    | exact superpose eq2866 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq11 (σ y) (σ x)
       have r₂ := eq2866
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq2866
       grind)
    | exact resolve eq11 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866
  have eq3056 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3053
  have eq3057 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3056
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq3056
    | exact resolve eq3056 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3056
  have eq3058 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3052
       have i₂ := eq26 x
       grind)
    | exact superpose eq26 eq3052
    | exact resolve eq3052 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3052
  have eq3061 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3057
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq3057
    | exact resolve eq3057 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057
  have eq3062 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3058
       have i₂ := eq13 y x
       grind)
    | exact superpose eq13 eq3058
    | exact resolve eq3058 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3058
  have eq3063 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3062
       have r₂ := eq3061
       grind)
    | exact resolve eq3062 eq3061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3061 eq3062
  have eq3681 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2220 y x
       have i₂ := eq3063
       grind)
    | exact superpose eq3063 eq2220
    | (have j0 := eq2220 y x
       grind)
    | exact resolve eq2220 eq3063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220 eq3063
  have eq3729 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq3681
  have eq3754 : x = (M.op x y) := by
    first
    | (have r₁ := eq3729
       have r₂ := eq3051
       grind)
    | exact resolve eq3729 eq3051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051 eq3729
  have eq4034 : x ≠ (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq3754
       grind)
    | exact superpose eq3754 eq10
    | exact resolve eq10 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4035 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq3754
       grind)
    | exact superpose eq3754 eq11
    | (have j0 := eq11 y x
       grind)
    | (have r₁ := eq11 y x
       have r₂ := eq3754
       grind)
    | exact resolve eq11 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4037 : x = (M.op x x) ∨ x = (k y x) := by grind
  clear eq4035
  have eq4038 : x = (k y x) := by
    first
    | (have r₁ := eq4034
       have r₂ := eq4037
       grind)
    | exact resolve eq4034 eq4037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034 eq4037
  have eq4343 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq609 x y
       have i₂ := eq4038
       grind)
    | exact superpose eq4038 eq609
    | (have j0 := eq609 x y
       grind)
    | exact resolve eq609 eq4038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609 eq4038
  have eq4350 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4343
  have eq5221 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq14
       have i₂ := eq4350
       grind)
    | exact superpose eq4350 eq14
    | exact resolve eq14 eq4350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4350
  have eq5231 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq5221
       have i₂ := eq3754
       grind)
    | exact superpose eq3754 eq5221
    | exact resolve eq5221 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754 eq5221
  have eq5232 : False := by grind
  exact eq5232

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq39 (σ X1) (σ X0)
       grind)
    | exact superpose eq39 eq13
    | (have j1 := eq39 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq39 X1 (τ X0)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq39
  have eq205 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq58
    | exact resolve eq58 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq227 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq205
    | (have j0 := eq205 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq205 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq584 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq14
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq686 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq584
       have i₂ := eq227 x y
       grind)
    | exact superpose eq227 eq584
    | (have j1 := eq227 (σ x) (σ y)
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 x y
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq584 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq584
  have eq687 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq686
  have eq780 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq8
    | exact resolve eq8 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq815 : x = y ∨ x = y := by
    first
    | (have i₁ := eq780
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq780
    | exact resolve eq780 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq816 : x = y := by grind
  clear eq815
  have eq991 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq14
    | exact resolve eq14 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq992 : False := by grind
  exact eq992

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_x_pxy_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq39 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq39 (σ X1) (σ X0)
       grind)
    | exact superpose eq39 eq13
    | (have j1 := eq39 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq13 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1
       have i₂ := eq39 X1 (τ X0)
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq39
  have eq205 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) X1
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq58
    | exact resolve eq58 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq227 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq205
    | (have j0 := eq205 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq205 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq584 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq14
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq686 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq584
       have i₂ := eq227 x y
       grind)
    | exact superpose eq227 eq584
    | (have j1 := eq227 (σ x) (σ y)
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 x y
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq584
       have r₂ := eq227 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq584 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq584
  have eq687 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq686
  have eq780 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq687
       grind)
    | exact superpose eq687 eq8
    | exact resolve eq8 eq687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq815 : x = y ∨ x = y := by
    first
    | (have i₁ := eq780
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq780
    | exact resolve eq780 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780
  have eq816 : x = y := by grind
  clear eq815
  have eq991 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq816
       grind)
    | exact superpose eq816 eq14
    | exact resolve eq14 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq992 : False := by grind
  exact eq992

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq12 X2 X0
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X2 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X2 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X2 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X2 X2
       have j1 := eq36 X0 X2 X2
       grind)
    | (have r₁ := eq31 X0 X1 X2
       have r₂ := eq36 X0 X1 X2
       grind)
    | (have r₁ := eq31 X0 X2 X1
       have r₂ := eq36 X0 X1 X2
       grind)
    | (have r₁ := eq31 (M.op X0 X1) X1 (M.op X0 X2)
       have r₂ := eq36 X0 X1 X2
       grind)
    | exact resolve eq31 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq36
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq38
    | (have j0 := eq38 (σ (k X0 X1)) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq38 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq114 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq115 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq198 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq205 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq198 X1 X0
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq198 X0 X1
       have r₂ := eq78 (M.op X0 X0) (k X1 X0)
       grind)
    | (have r₁ := eq198 X0 X1
       have r₂ := eq78 (k X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq198 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq198
  have eq261 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq116 (τ X1) X0
       grind)
    | exact superpose eq116 eq16
    | (have j1 := eq116 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq116
  have eq565 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq261 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq261
    | exact resolve eq261 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq598 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq565
    | (have j0 := eq565 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq565 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq613 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq205 x y
       grind)
    | exact superpose eq205 eq14
    | (have j1 := eq205 x y
       grind)
    | exact resolve eq14 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq916 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq613
       have i₂ := eq598 y x
       grind)
    | exact superpose eq598 eq613
    | (have j1 := eq598 (σ x) (σ y)
       grind)
    | (have r₁ := eq613
       have r₂ := eq598 y x
       grind)
    | (have r₁ := eq613
       have r₂ := eq598 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq613
       have r₂ := eq598 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq613 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq613
  have eq917 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq916
  have eq1029 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq917
       grind)
    | exact superpose eq917 eq8
    | exact resolve eq8 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq1065 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1029
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1029
    | exact resolve eq1029 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1066 : x = y := by grind
  clear eq1065
  have eq1166 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1066
       grind)
    | exact superpose eq1066 eq14
    | exact resolve eq14 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1167 : False := by grind
  exact eq1167

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq12 X2 X0
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq12 X2 X0
       grind)
    | exact resolve eq12 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X2 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X0 X0
       have i₂ := eq12 X0 X0
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X2 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X2 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X2 X2
       have j1 := eq36 X0 X2 X2
       grind)
    | (have r₁ := eq31 X0 X1 X2
       have r₂ := eq36 X0 X1 X2
       grind)
    | (have r₁ := eq31 X0 X2 X1
       have r₂ := eq36 X0 X1 X2
       grind)
    | (have r₁ := eq31 (M.op X0 X1) X1 (M.op X0 X2)
       have r₂ := eq36 X0 X1 X2
       grind)
    | exact resolve eq31 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq36
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq38
    | (have j0 := eq38 (σ (k X0 X1)) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq38 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq114 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq115 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq115 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq198 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq205 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq198 X1 X0
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq198 X0 X1
       have r₂ := eq78 (M.op X0 X0) (k X1 X0)
       grind)
    | (have r₁ := eq198 X0 X1
       have r₂ := eq78 (k X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq198 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq198
  have eq261 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq116 (τ X1) X0
       grind)
    | exact superpose eq116 eq16
    | (have j1 := eq116 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq116
  have eq565 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq261 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq261
    | exact resolve eq261 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq598 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq565 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq565
    | (have j0 := eq565 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq565 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq613 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq205 x y
       grind)
    | exact superpose eq205 eq14
    | (have j1 := eq205 x y
       grind)
    | exact resolve eq14 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq916 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq613
       have i₂ := eq598 y x
       grind)
    | exact superpose eq598 eq613
    | (have j1 := eq598 (σ x) (σ y)
       grind)
    | (have r₁ := eq613
       have r₂ := eq598 y x
       grind)
    | (have r₁ := eq613
       have r₂ := eq598 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq613
       have r₂ := eq598 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq613 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq613
  have eq917 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq916
  have eq1029 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq917
       grind)
    | exact superpose eq917 eq8
    | exact resolve eq8 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq1065 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1029
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1029
    | exact resolve eq1029 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1066 : x = y := by grind
  clear eq1065
  have eq1166 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1066
       grind)
    | exact superpose eq1066 eq14
    | exact resolve eq14 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066
  have eq1167 : False := by grind
  exact eq1167

/-- `x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y`
for `x`, `y`.  Vampire refutation replayed step by step.

The source axiom is **absent**: a bijection commuting with this `□` is an automorphism of `◇` in
every magma, so the obligation holds of every law and the guard device costs only its target half
from here on. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_all (L : Law.MagmaLaw ℕ) :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) L := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M _ σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq8 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq9 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq14 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear ht hu hv hd nh hi1 hi2
  have eq16 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq13
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq10 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq22 (σ X0)
       grind)
    | exact superpose eq22 eq13
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq24 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24
  have eq32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact superpose eq12 eq13
    | (have j1 := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X0
       have i₂ := eq12 X1 X0
       grind)
    | (have i₁ := eq10 X1 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq10
    | (have j0 := eq10 X0 X0
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq10 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq10 X0 X1
       have r₂ := eq12 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq10 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq27 X0
       grind)
    | exact superpose eq27 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | exact resolve eq32 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (σ X1) (σ X0)
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq38
    | (have j0 := eq38 (σ (k X0 X1)) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq38 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq69 X0 X1
       have r₂ := eq12 (M.op X1 X0) (M.op X1 X1)
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq153 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq160 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq153 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq153 X0 X1
       have r₂ := eq77 (M.op X0 X0) (k X1 X0)
       grind)
    | (have r₁ := eq153 X0 X1
       have r₂ := eq77 (k X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq153 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq153
  have eq276 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq72 (τ X1) X0
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16 eq72
  have eq576 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 (σ X0)
       have i₂ := eq8 X0
       grind)
    | exact superpose eq8 eq276
    | exact resolve eq276 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq613 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq576 X0 X1
       have i₂ := eq13 X0 X1
       grind)
    | exact superpose eq13 eq576
    | (have j0 := eq576 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq576 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq630 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14
       have i₂ := eq160 x y
       grind)
    | exact superpose eq160 eq14
    | (have j1 := eq160 x y
       grind)
    | exact resolve eq14 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq1083 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq630
       have i₂ := eq613 y x
       grind)
    | exact superpose eq613 eq630
    | (have j1 := eq613 (σ x) (σ y)
       grind)
    | (have r₁ := eq630
       have r₂ := eq613 y x
       grind)
    | (have r₁ := eq630
       have r₂ := eq613 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq630
       have r₂ := eq613 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq630 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq630
  have eq1084 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1083
  have eq1200 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq8 y
       have i₂ := eq1084
       grind)
    | exact superpose eq1084 eq8
    | exact resolve eq8 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1235 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1200
       have i₂ := eq8 x
       grind)
    | exact superpose eq8 eq1200
    | exact resolve eq1200 eq8
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq1236 : x = y := by grind
  clear eq1235
  have eq1367 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq14
       have i₂ := eq1236
       grind)
    | exact superpose eq1236 eq14
    | exact resolve eq14 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1368 : False := by grind
  exact eq1368
