import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_pyx_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq77 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : y ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k y x) := by
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
  have eq81 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq99
    | (have j0 := eq99 (σ X0) (σ X1)
       grind)
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq99 y x
       grind)
    | exact superpose eq99 eq77
    | (have j1 := eq99 y x
       grind)
    | exact resolve eq77 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq122
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq99
    | (have j0 := eq99 (σ y) (σ x)
       grind)
    | exact resolve eq99 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq129
       have r₂ := eq27
       grind)
    | exact resolve eq129 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq134 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq132
    | exact resolve eq132 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq136 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq27
    | exact resolve eq27 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq155 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq144 eq16
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq662 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq81
    | (have r₁ := eq81
       have r₂ := eq134
       grind)
    | exact resolve eq81 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq134
  have eq663 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq662
  have eq768 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq663 eq125
    | exact resolve eq125 eq663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq772 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq768
  have eq777 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq772
       have r₂ := eq136
       grind)
    | exact resolve eq772 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq772
  have eq785 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq777 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq777
       grind)
    | exact resolve eq13 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq787 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq785
  have eq789 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq787
    | exact resolve eq787 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq932 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq789 eq125
    | exact resolve eq125 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq789
  have eq935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq932
  have eq939 : y = (M.op x y) := by
    first
    | (have r₁ := eq935
       have r₂ := eq27
       grind)
    | exact resolve eq935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq941 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq939 eq20
    | exact resolve eq20 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : y ≠ y ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq939 eq80
    | (have r₁ := eq80
       have r₂ := eq939
       grind)
    | exact resolve eq80 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq950 : y = (M.op y x) ∨ y = (k y x) := by grind
  clear eq945
  have eq957 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq941
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq941
    | exact resolve eq941 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq1089 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq957 eq26
    | exact resolve eq26 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1165 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq103
    | (have j0 := eq103 (M.op x y) X0
       grind)
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq103
  have eq1188 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq939 eq1165
    | (have j0 := eq1165 X0
       grind)
    | exact resolve eq1165 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq2284 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1188 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1188
    | (have j0 := eq1188 x
       grind)
    | exact resolve eq1188 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1188
  have eq2306 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1089 eq2284
    | exact resolve eq2284 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284
  have eq2322 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2306
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq2306
    | exact resolve eq2306 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2306
  have eq2332 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq957 eq2322
    | exact resolve eq2322 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2322
  have eq2336 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1089 eq2332
    | exact resolve eq2332 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089 eq2332
  have eq2337 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq2336
       have r₂ := eq27
       grind)
    | exact resolve eq2336 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336
  have eq2339 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq2337 eq155
    | exact resolve eq155 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq2337
  have eq2341 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq939 eq2339
    | exact resolve eq2339 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339
  have eq2439 : y = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq950
       have i₂ := eq2341
       grind)
    | exact superpose eq2341 eq950
    | exact resolve eq950 eq2341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq2442 : y ≠ y ∨ (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2439
       grind)
    | exact superpose eq2439 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2439
       grind)
    | exact resolve eq13 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq2451 : (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2442
  have eq2452 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2451
       have i₂ := eq2341
       grind)
    | exact superpose eq2341 eq2451
    | exact resolve eq2451 eq2341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2341 eq2451
  have eq2454 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2452
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2452
    | exact resolve eq2452 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2452
  have eq2456 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq939 eq2454
    | exact resolve eq2454 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939 eq2454
  have eq2457 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2456
  have eq2464 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2457 eq15
    | exact resolve eq15 eq2457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2457
  have eq2465 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2464
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2464
    | exact resolve eq2464 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2464
  have eq2469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq957 eq2465
    | exact resolve eq2465 eq957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957 eq2465
  have eq2473 : False := by grind
  exact eq2473

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pyx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq17
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X4) X3) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 X2) X0 X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq52 (M.op X0 X0) X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X2 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq52 X1 X2 X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X3 X3) (M.op X0 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X3 (M.op X0 X4) X2
       have i₂ := eq52 X0 X4 X2 X1
       grind)
    | (have i₁ := eq9 X3 (M.op X0 X4) X2
       have i₂ := eq52 X0 X1 X2 X4
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X1) X2) ∨ (k (M.op X2 X2) X0) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 X2) X0
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq12 (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X2 X2) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X2) (M.op X1 X2)) X1
       have r₂ := eq9 (M.op X1 X2) X1 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq642 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq642
    | (have j0 := eq642 X0 (σ X1)
       grind)
    | exact resolve eq642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op X3 X4) X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq70 X2 X3 X4 X0 X5
       have i₂ := eq71 (M.op X2 X2) X3 X0 X1
       grind)
    | (have i₁ := eq70 X2 X3 X4 X0 X5
       have i₂ := eq71 X0 X1 (M.op X2 X2) X3
       grind)
    | exact superpose eq71 eq70
    | exact resolve eq70 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq71
  have eq1049 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X0) (M.op X2 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq86 X2 X3 (M.op X2 X3) X0 X4
       have i₂ := eq9 (M.op X2 X3) X0 X1
       grind)
    | (have i₁ := eq86 X0 X1 X2 X0 X4
       have i₂ := eq9 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1708 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq643 y x
       grind)
    | exact superpose eq643 eq16
    | (have j1 := eq643 x x
       grind)
    | exact resolve eq16 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1721 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq643 X0 X1
       grind)
    | exact superpose eq643 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq643 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq643 X0 X1
       grind)
    | exact resolve eq12 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1739 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq643 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq1740 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1721 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1721
    | (have j0 := eq1721 X0 X1
       grind)
    | exact resolve eq1721 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721
  have eq2354 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) = (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq4437 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1739 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1739
    | (have j0 := eq1739 (τ X0)
       grind)
    | exact resolve eq1739 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4447 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4437 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4437
    | (have j0 := eq4437 X0
       grind)
    | exact resolve eq4437 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4437
  have eq4454 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4447 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4447
    | (have j0 := eq4447 X0
       grind)
    | exact resolve eq4447 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4447
  have eq13376 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1708
       have i₂ := eq642 y x
       grind)
    | exact superpose eq642 eq1708
    | (have j1 := eq642 x (σ x)
       grind)
    | exact resolve eq1708 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708
  have eq13379 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq13376
  have eq13417 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq13379
       grind)
    | exact superpose eq13379 eq12
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq13379
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq13379
       grind)
    | exact resolve eq12 eq13379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13379
  have eq13474 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq13417
  have eq13476 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13474
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq13474
    | exact resolve eq13474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13474
  have eq13482 : (k x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq13476
       grind)
    | exact superpose eq13476 eq10
    | exact resolve eq10 eq13476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13476
  have eq13506 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13482
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13482
    | exact resolve eq13482 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13482
  have eq13507 : x = (M.op x x) := by
    first
    | (have j1 := eq4454 x
       grind)
    | (have r₁ := eq13506
       have r₂ := eq4454 x
       grind)
    | exact resolve eq13506 eq4454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454 eq13506
  have eq13508 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1
       have i₂ := eq13507
       grind)
    | exact superpose eq13507 eq9
    | exact resolve eq9 eq13507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13544 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq13507
       grind)
    | exact superpose eq13507 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq13507
       grind)
    | exact resolve eq12 eq13507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13545 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x x X0 X1
       have i₂ := eq13507
       grind)
    | exact superpose eq13507 eq52
    | exact resolve eq52 eq13507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq13601 : x = (k x x) := by grind
  clear eq13544
  have eq13631 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1739 x
       have i₂ := eq13601
       grind)
    | exact superpose eq13601 eq1739
    | (have j0 := eq1739 x
       grind)
    | exact resolve eq1739 eq13601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739 eq13601
  have eq13636 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq13631
  have eq13773 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq13508 (M.op X0 X1) x
       have i₂ := eq13508 X0 X1
       grind)
    | exact superpose eq13508 eq13508
    | exact resolve eq13508 eq13508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13805 : (M.op x (σ x)) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq13508 (σ x) (σ x)
       have i₂ := eq13636
       grind)
    | exact superpose eq13636 eq13508
    | exact resolve eq13508 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14053 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13773 X0 X1
       have i₂ := eq13508 x X0
       grind)
    | exact superpose eq13508 eq13773
    | exact resolve eq13773 eq13508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13773
  have eq14144 : ∀ X0 X1 : G, x = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14053 X0 X1
       have i₂ := eq13507
       grind)
    | exact superpose eq13507 eq14053
    | exact resolve eq14053 eq13507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13507 eq14053
  have eq14277 : x = (M.op x (σ x)) := by
    first
    | (have i₁ := eq14144 (σ x) (σ x)
       have i₂ := eq13636
       grind)
    | exact superpose eq13636 eq14144
    | exact resolve eq14144 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14282 : ∀ X0 X1 : G, x ≠ x ∨ (M.op (M.op X0 X1) x) = (k x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 x (M.op X0 X1)
       have i₂ := eq14144 X0 X1
       grind)
    | exact superpose eq14144 eq12
    | (have j0 := eq12 x (M.op X0 X1)
       grind)
    | (have r₁ := eq12 x (M.op X0 X1)
       have r₂ := eq14144 X0 X1
       grind)
    | exact resolve eq12 eq14144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14343 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (k x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14282 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14282
  have eq14382 : ∀ X0 X1 : G, (M.op x X0) = (k x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14343 X0 X1
       have i₂ := eq13508 X0 X1
       grind)
    | exact superpose eq13508 eq14343
    | exact resolve eq14343 eq13508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13508 eq14343
  have eq14594 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x X0) X1) = (M.op (M.op X1 X2) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq745 X1 X2 X3 x x X0
       have i₂ := eq13545 X0 x
       grind)
    | exact superpose eq13545 eq745
    | exact resolve eq745 eq13545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq14814 : ∀ X1 X2 X3 : G, (M.op x X1) = (M.op (M.op X1 X2) (M.op X3 X3)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq14594 x X1 X2 X3
       have i₂ := eq13545 X1 x
       grind)
    | exact superpose eq13545 eq14594
    | exact resolve eq14594 eq13545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13545 eq14594
  have eq15039 : x = (M.op (σ x) x) := by
    first
    | (have i₁ := eq13805
       have i₂ := eq14277
       grind)
    | exact superpose eq14277 eq13805
    | exact resolve eq13805 eq14277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13805 eq14277
  have eq15095 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ x)) (M.op X0 X2)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1049 (σ x) x X0 X1 X2
       have i₂ := eq15039
       grind)
    | exact superpose eq15039 eq1049
    | exact resolve eq1049 eq15039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049 eq15039
  have eq15103 : ∀ X0 X2 : G, x = (M.op (M.op (σ x) (σ x)) (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq15095 X0 x X2
       have i₂ := eq14144 X0 x
       grind)
    | exact superpose eq14144 eq15095
    | exact resolve eq15095 eq14144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15095
  have eq15153 : ∀ X0 X2 : G, x = (M.op (σ x) (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq15103 X0 X2
       have i₂ := eq13636
       grind)
    | exact superpose eq13636 eq15103
    | exact resolve eq15103 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15103
  have eq15228 : x = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15153 (σ x) (σ x)
       have i₂ := eq13636
       grind)
    | exact superpose eq13636 eq15153
    | exact resolve eq15153 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15153
  have eq15365 : x = (σ x) := by
    first
    | (have i₁ := eq15228
       have i₂ := eq13636
       grind)
    | exact superpose eq13636 eq15228
    | exact resolve eq15228 eq13636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13636 eq15228
  have eq15563 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15365
       grind)
    | exact superpose eq15365 eq16
    | exact resolve eq16 eq15365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15574 : ∀ X0 : G, (k x (τ X0)) = (τ (k x X0)) := by
    intro X0
    first
    | (have i₁ := eq28 x X0
       have i₂ := eq15365
       grind)
    | exact superpose eq15365 eq28
    | exact resolve eq28 eq15365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq15914 : ∀ X0 X1 : G, (τ (M.op x X0)) = (k x (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15574 (M.op X0 X1)
       have i₂ := eq14382 X0 X1
       grind)
    | exact superpose eq14382 eq15574
    | exact resolve eq15574 eq14382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15574
  have eq17657 : ∀ X0 : G, (k (M.op x X0) X0) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq2354 x x
       have i₂ := eq14814 x x x
       grind)
    | exact superpose eq14814 eq2354
    | exact resolve eq2354 eq14814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354 eq14814
  have eq21290 : ∀ X0 : G, (k (τ (M.op x (σ X0))) X0) = (τ (M.op (σ X0) (M.op x (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op x (σ X0)) X0
       have i₂ := eq17657 (σ X0)
       grind)
    | exact superpose eq17657 eq22
    | exact resolve eq22 eq17657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17657
  have eq61720 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k x (k (τ (M.op x (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq15914 (σ X0) (M.op x (σ X0))
       have i₂ := eq21290 X0
       grind)
    | exact superpose eq21290 eq15914
    | exact resolve eq15914 eq21290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15914 eq21290
  have eq61869 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k x (M.op X0 (τ (M.op x (σ X0))))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61720 X0
       have i₂ := eq642 (τ (M.op x (σ X0))) X0
       grind)
    | exact superpose eq642 eq61720
    | (have j1 := eq642 X0 X0
       grind)
    | exact resolve eq61720 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq61720
  have eq61962 : ∀ X0 : G, (M.op x X0) = (τ (M.op x (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq61869 X0
       have i₂ := eq14382 X0 (τ (M.op x (σ X0)))
       grind)
    | exact superpose eq14382 eq61869
    | (have j0 := eq61869 X0
       grind)
    | exact resolve eq61869 eq14382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14382 eq61869
  have eq62112 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op x (σ X0))
       have i₂ := eq61962 X0
       grind)
    | exact superpose eq61962 eq11
    | (have j1 := eq61962 X0
       grind)
    | exact resolve eq11 eq61962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61962
  have eq62231 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15563
       have i₂ := eq62112 y
       grind)
    | exact superpose eq62112 eq15563
    | (have j1 := eq62112 y
       grind)
    | (have r₁ := eq15563
       have r₂ := eq62112 y
       grind)
    | exact resolve eq15563 eq62112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62112
  have eq62299 : y = (M.op y y) := by grind
  clear eq62231
  have eq62411 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq62299
       grind)
    | exact superpose eq62299 eq12
    | (have r₁ := eq12 y y
       have r₂ := eq62299
       grind)
    | exact resolve eq12 eq62299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62473 : x = (M.op x y) := by
    first
    | (have i₁ := eq14144 y y
       have i₂ := eq62299
       grind)
    | exact superpose eq62299 eq14144
    | exact resolve eq14144 eq62299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62299
  have eq62500 : y = (k y y) := by grind
  clear eq62411
  have eq62592 : (σ x) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq15563
       have i₂ := eq62473
       grind)
    | exact superpose eq62473 eq15563
    | exact resolve eq15563 eq62473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15563 eq62473
  have eq62767 : x ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq62592
       have i₂ := eq15365
       grind)
    | exact superpose eq15365 eq62592
    | exact resolve eq62592 eq15365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15365 eq62592
  have eq62837 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1740 y y
       have i₂ := eq62500
       grind)
    | exact superpose eq62500 eq1740
    | (have j0 := eq1740 x y
       grind)
    | exact resolve eq1740 eq62500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740 eq62500
  have eq62871 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq62837
  have eq62872 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq62871
  have eq63645 : x = (M.op x (σ y)) := by
    first
    | (have i₁ := eq14144 (σ y) (σ y)
       have i₂ := eq62872
       grind)
    | exact superpose eq62872 eq14144
    | exact resolve eq14144 eq62872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14144 eq62872
  have eq63682 : False := by grind
  exact eq63682

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq48 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq48 (σ X0)
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq62
    | exact resolve eq62 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq62
  have eq85 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X0 X1) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85
    | (have j0 := eq85 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq85 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq16
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq651 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq287
       have i₂ := eq85 y x
       grind)
    | exact superpose eq85 eq287
    | (have j1 := eq85 (σ x) (σ y)
       grind)
    | (have r₁ := eq287
       have r₂ := eq85 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq287
       have r₂ := eq85 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq287 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq287
  have eq654 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq651
  have eq655 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq654
       grind)
    | exact superpose eq654 eq16
    | exact resolve eq16 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq656 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq655
       have r₂ := eq71 x
       grind)
    | exact resolve eq655 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq695 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq656
       grind)
    | exact superpose eq656 eq10
    | exact resolve eq10 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq712 : x = y := by
    first
    | (have i₁ := eq695
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq695
    | exact resolve eq695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq759 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq712
       grind)
    | exact superpose eq712 eq16
    | exact resolve eq16 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq760 : False := by grind
  exact eq760

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pyx_pxy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq97 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq2553 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq97 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq12 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2554 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq97 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2604 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2554 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2554
  have eq2611 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2604 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2604 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq2604 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq2604 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2604
  have eq2612 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2553 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq2553 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq2553 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2553
  have eq2619 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2611 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2611
    | (have j0 := eq2611 X0 X1
       grind)
    | exact resolve eq2611 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611
  have eq2620 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq2621 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2612 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2612
    | (have j0 := eq2612 X0 X1
       grind)
    | exact resolve eq2612 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2612
  have eq2622 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2621 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621
  have eq2625 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2622 X0 X1
       have j1 := eq2620 X0 X1
       grind)
    | (have r₁ := eq2622 X0 X1
       have r₂ := eq2620 X0 X1
       grind)
    | exact resolve eq2622 eq2620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2620 eq2622
  have eq2626 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2625 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2625
    | exact resolve eq2625 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2640 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2625 x y
       grind)
    | exact superpose eq2625 eq16
    | exact resolve eq16 eq2625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2625
  have eq2856 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq2626 X0 (τ X1)
       grind)
    | exact superpose eq2626 eq17
    | exact resolve eq17 eq2626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2626
  have eq2892 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2856 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2856
    | exact resolve eq2856 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856
  have eq2909 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2892 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2892
    | exact resolve eq2892 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892
  have eq2946 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2640
       have i₂ := eq2909 x y
       grind)
    | exact superpose eq2909 eq2640
    | exact resolve eq2640 eq2909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640 eq2909
  have eq2947 : False := by grind
  exact eq2947

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  have eq77 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (k y x) := by
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
  have eq81 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq99
    | (have j0 := eq99 (σ X0) (σ X1)
       grind)
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq99 y x
       grind)
    | exact superpose eq99 eq77
    | (have j1 := eq99 y x
       grind)
    | exact resolve eq77 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq122
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq99
    | (have j0 := eq99 (σ y) (σ x)
       grind)
    | exact resolve eq99 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq129
       have r₂ := eq27
       grind)
    | exact resolve eq129 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq134 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq132
    | exact resolve eq132 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq136 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq27
    | exact resolve eq27 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq155 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq144 eq16
    | exact resolve eq16 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq650 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq81
    | (have r₁ := eq81
       have r₂ := eq134
       grind)
    | exact resolve eq81 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq134
  have eq651 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq650
  have eq777 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq651 eq125
    | exact resolve eq125 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq781 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq777
  have eq786 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq781
       have r₂ := eq136
       grind)
    | exact resolve eq781 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq781
  have eq795 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq786 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq786
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq786
       grind)
    | exact resolve eq13 eq786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq797 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq795
  have eq801 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq797
    | exact resolve eq797 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq946 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq801 eq125
    | exact resolve eq125 eq801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq801
  have eq949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq946
  have eq953 : y = (M.op x y) := by
    first
    | (have r₁ := eq949
       have r₂ := eq27
       grind)
    | exact resolve eq949 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq955 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq953 eq20
    | exact resolve eq20 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq959 : y ≠ y ∨ x = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq953 eq80
    | (have r₁ := eq80
       have r₂ := eq953
       grind)
    | exact resolve eq80 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq964 : x = (M.op y x) ∨ y = (k y x) := by grind
  clear eq959
  have eq972 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq955
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq955
    | exact resolve eq955 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1104 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq972 eq26
    | exact resolve eq26 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1273 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq103
    | (have j0 := eq103 (M.op x y) X0
       grind)
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq103
  have eq1298 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq953 eq1273
    | (have j0 := eq1273 X0
       grind)
    | exact resolve eq1273 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq2185 : (σ (k y x)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1298 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1298
    | (have j0 := eq1298 x
       grind)
    | exact resolve eq1298 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1298
  have eq2206 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1104 eq2185
    | exact resolve eq2185 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185
  have eq2222 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2206
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq2206
    | exact resolve eq2206 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2206
  have eq2234 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq972 eq2222
    | exact resolve eq2222 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq2239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1104 eq2234
    | exact resolve eq2234 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq2234
  have eq2240 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq2239
       have r₂ := eq27
       grind)
    | exact resolve eq2239 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq2242 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) x) := by
    first
    | exact superpose eq2240 eq155
    | exact resolve eq155 eq2240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq2240
  have eq2244 : (k y x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq953 eq2242
    | exact resolve eq2242 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq2365 : x = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq964
       have i₂ := eq2244
       grind)
    | exact superpose eq2244 eq964
    | exact resolve eq964 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq2378 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2365
       grind)
    | exact superpose eq2365 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2365
       grind)
    | exact resolve eq13 eq2365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq2388 : (M.op x y) = (k y x) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2378
  have eq2396 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2388
       have i₂ := eq2244
       grind)
    | exact superpose eq2244 eq2388
    | exact resolve eq2388 eq2244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244 eq2388
  have eq2403 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2396
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2396
    | exact resolve eq2396 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2396
  have eq2405 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq953 eq2403
    | exact resolve eq2403 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq953 eq2403
  have eq2406 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2405
  have eq2413 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2406 eq15
    | exact resolve eq15 eq2406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2406
  have eq2414 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2413
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2413
    | exact resolve eq2413 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2413
  have eq2418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq972 eq2414
    | exact resolve eq2414 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq2414
  have eq2422 : False := by grind
  exact eq2422

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq77 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
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
  have eq81 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq99 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq99
    | (have j0 := eq99 (σ X0) (σ X1)
       grind)
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq99 y x
       grind)
    | exact superpose eq99 eq77
    | (have j1 := eq99 y x
       grind)
    | exact resolve eq77 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq122
    | exact resolve eq122 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq124
    | exact resolve eq124 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq125 eq99
    | (have j0 := eq99 (σ y) (σ x)
       grind)
    | exact resolve eq99 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq129
       have r₂ := eq27
       grind)
    | exact resolve eq129 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq134 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq132
    | exact resolve eq132 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq136 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq134 eq27
    | exact resolve eq27 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq134 eq81
    | (have r₁ := eq81
       have r₂ := eq134
       grind)
    | exact resolve eq81 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq134
  have eq576 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq575
  have eq1277 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq103 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq18790 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq576 eq125
    | exact resolve eq125 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq18796 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq18790
  have eq18801 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18796
       have r₂ := eq136
       grind)
    | exact resolve eq18796 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq18796
  have eq18805 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18801 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18801
       grind)
    | exact resolve eq13 eq18801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18801
  have eq18844 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18805
  have eq18851 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18844
    | exact resolve eq18844 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18844
  have eq18859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18851 eq125
    | exact resolve eq125 eq18851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq18851
  have eq18863 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18859
  have eq18867 : x = (M.op x y) := by
    first
    | (have r₁ := eq18863
       have r₂ := eq27
       grind)
    | exact resolve eq18863 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18863
  have eq18869 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18867 eq20
    | exact resolve eq20 eq18867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq18873 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | exact superpose eq18867 eq80
    | (have r₁ := eq80
       have r₂ := eq18867
       grind)
    | exact resolve eq80 eq18867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq18888 : x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq18873
  have eq18902 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18869
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18869
    | exact resolve eq18869 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18869
  have eq23300 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1277 x y
       have i₂ := eq18888
       grind)
    | exact superpose eq18888 eq1277
    | (have j0 := eq1277 x y
       grind)
    | exact resolve eq1277 eq18888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18888
  have eq23303 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq23300
  have eq23308 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq23303
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23303
    | exact resolve eq23303 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23303
  have eq23311 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq23308
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23308
    | exact resolve eq23308 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23308
  have eq23313 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq23311
    | exact resolve eq23311 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23311
  have eq23315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq18902 eq23313
    | exact resolve eq23313 eq18902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23313
  have eq23316 : x = (M.op y x) := by
    first
    | (have r₁ := eq23315
       have r₂ := eq27
       grind)
    | exact resolve eq23315 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23315
  have eq23318 : x ≠ x ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq23316
       grind)
    | exact superpose eq23316 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq23316
       grind)
    | exact resolve eq13 eq23316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23316
  have eq23354 : (M.op x y) = (k y x) := by grind
  clear eq23318
  have eq23371 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq23354
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23354
    | exact resolve eq23354 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq23354
  have eq23382 : x = (k y x) := by
    first
    | exact superpose eq18867 eq23371
    | exact resolve eq23371 eq18867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18867 eq23371
  have eq23404 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1277 x y
       have i₂ := eq23382
       grind)
    | exact superpose eq23382 eq1277
    | (have j0 := eq1277 x y
       grind)
    | exact resolve eq1277 eq23382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq23382
  have eq23407 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23404
  have eq23412 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23407
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23407
    | exact resolve eq23407 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq23407
  have eq23415 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq23412
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23412
    | exact resolve eq23412 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23412
  have eq23417 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq23415
    | exact resolve eq23415 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq23415
  have eq23419 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18902 eq23417
    | exact resolve eq23417 eq18902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18902 eq23417
  have eq23420 : False := by grind
  exact eq23420

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pxy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq28 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28
    | (have j0 := eq28 x
       grind)
    | exact resolve eq28 eq22
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq81 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) x
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq86 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1
       have i₂ := eq81 X0 x
       grind)
    | exact superpose eq81 eq9
    | exact resolve eq9 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq58 x
       have i₂ := eq81 sF2 x
       grind)
    | exact superpose eq81 eq58
    | exact resolve eq58 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq104 x
       have i₂ := eq57 sF0 sF2 x
       grind)
    | exact superpose eq57 eq104
    | exact resolve eq104 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq108 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq86 eq58
    | exact resolve eq58 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq114 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq9 sF2 sF4 (M.op sF2 X0)
       grind)
    | exact superpose eq9 eq110
    | exact resolve eq110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq115 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq105 eq114
    | exact resolve eq114 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq114
  have eq116 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq108 eq115
    | exact resolve eq115 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq119 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (M.op X0 X1) x
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq92 (M.op x y) X0
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq92
    | exact resolve eq92 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (M.op (M.op x y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) x) := by
    first
    | exact superpose eq94 eq92
    | exact resolve eq92 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq123
       have i₂ := eq9 x sF0 sF2
       grind)
    | exact superpose eq9 eq123
    | exact resolve eq123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq134 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 sF0 X1
       have i₂ := eq9 sF0 x x
       grind)
    | (have i₁ := eq119 x X1
       have i₂ := eq9 x sF0 x
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq137 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq131
       have i₂ := eq81 sF0 x
       grind)
    | exact superpose eq81 eq131
    | exact resolve eq131 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq139 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 X1
       have i₂ := eq81 sF0 x
       grind)
    | exact superpose eq81 eq134
    | exact resolve eq134 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq145 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X2 X2) (M.op X2 X2)) ∨ (M.op (M.op X0 X1) X2) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq12 X0 (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X1 X2) (M.op X1 X2)) ∨ (M.op (M.op X0 X0) X1) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq12 X0 (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) X1) (M.op (σ x) X1)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq86 eq12
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq86 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq12 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  have eq150 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq61 eq150
    | exact resolve eq150 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq160 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) X1)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq86 eq148
    | (have j0 := eq148 X0 X1
       grind)
    | (have r₁ := eq148 (M.op (σ x) X1) X1
       have r₂ := eq86 (M.op (σ x) X1) X1
       grind)
    | (have r₁ := eq148 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq86 (M.op (σ x) (σ y)) (σ y)
       grind)
    | exact resolve eq148 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq167 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq116 eq160
    | (have j0 := eq160 X0 X1
       grind)
    | (have r₁ := eq160 (M.op x y) X0
       have r₂ := eq116 X0
       grind)
    | exact resolve eq160 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq160
  have eq185 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq153 (σ X0)
       grind)
    | exact superpose eq153 eq15
    | exact resolve eq15 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq153 X0
       grind)
    | exact superpose eq153 eq185
    | exact resolve eq185 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq185
  have eq203 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq108 (M.op X0 X1) x
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq108 (M.op x y) X0
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq108
    | exact resolve eq108 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) (σ x)) := by
    first
    | exact superpose eq94 eq108
    | exact resolve eq108 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq209
       have i₂ := eq57 sF0 sF2 sF2
       grind)
    | exact superpose eq57 eq209
    | exact resolve eq209 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq225 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq108 eq203
    | exact resolve eq203 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq229 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq108 eq221
    | exact resolve eq221 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq244 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq229 eq9
    | exact resolve eq9 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq225 eq12
    | (have j0 := eq12 (M.op x y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (M.op x y) (M.op (σ x) (σ y))
       have r₂ := eq225 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       grind)
    | (have r₁ := eq282 X0 X1
       have r₂ := eq229
       grind)
    | exact resolve eq282 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq307 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq287 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq287
    | (have j0 := eq287 x y
       grind)
    | exact resolve eq287 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq408 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq399
    | exact resolve eq399 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq410 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq408
    | exact resolve eq408 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq412 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq26 eq410
    | exact resolve eq410 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq414 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq412
       have r₂ := eq159
       grind)
    | exact resolve eq412 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq412
  have eq444 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op (σ x) (σ y)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq108 eq52
    | exact resolve eq52 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq451 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op x y) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq94 eq52
    | exact resolve eq52 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq52 X0 X0 X2 X1
       grind)
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq52 X0 X1 X2 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op X0 X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 X4
       have i₂ := eq52 X0 X2 (M.op X0 X2) X1
       grind)
    | (have i₁ := eq9 (M.op X0 X2) X3 X4
       have i₂ := eq52 X0 X1 (M.op X0 X2) X2
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 x
       have i₂ := eq57 sF0 sF2 x
       grind)
    | exact superpose eq57 eq451
    | exact resolve eq451 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq506 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X3) = (M.op (M.op X3 X4) (M.op X0 X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq486 X0 x X2 X3 X4
       have i₂ := eq444 X0 x (M.op X0 X2) X3
       grind)
    | (have i₁ := eq486 (σ x) (σ y) X2 X3 X4
       have i₂ := eq444 (M.op (σ x) X2) x X2 X3
       grind)
    | exact superpose eq444 eq486
    | exact resolve eq486 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq524 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq500 eq444
    | exact resolve eq444 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq527 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq500 eq88
    | exact resolve eq88 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq528 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq500 eq244
    | exact resolve eq244 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq530 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op X0 X2)) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X0 X2 X3 X4
    first
    | exact superpose eq500 eq506
    | exact resolve eq506 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500 eq506
  have eq549 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq414
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq414
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq414 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq549
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq549
    | exact resolve eq549 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq559
    | exact resolve eq559 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq561 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq560
       have r₂ := eq27
       grind)
    | exact resolve eq560 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq562 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq561
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq561
    | exact resolve eq561 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq563 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq562
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq562
    | exact resolve eq562 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq564 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq149
       have i₂ := eq563
       grind)
    | exact superpose eq563 eq149
    | (have r₁ := eq149
       have r₂ := eq563
       grind)
    | exact resolve eq149 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq563
  have eq575 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq564
  have eq578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq414
       have i₂ := eq575
       grind)
    | exact superpose eq575 eq414
    | exact resolve eq414 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq575
  have eq580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq578
  have eq581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq580
    | exact resolve eq580 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq582 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq581
       have r₂ := eq27
       grind)
    | exact resolve eq581 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq584 : (M.op (M.op x y) (σ x)) = (M.op (σ x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq94
    | exact resolve eq94 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : (M.op (M.op x y) (σ x)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq137
    | exact resolve eq137 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq587 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq582 eq225
    | exact resolve eq225 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq229
    | exact resolve eq229 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (M.op (σ x) (M.op x y)) = (k (M.op X0 X1) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq582 eq287
    | exact resolve eq287 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq590 : (M.op (σ x) (M.op x y)) = (k (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq307
    | exact resolve eq307 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq591 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq584 eq86
    | exact resolve eq86 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq584 eq108
    | exact resolve eq108 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq597
       have i₂ := eq57 sF0 sF2 sF2
       grind)
    | exact superpose eq57 eq597
    | exact resolve eq597 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq607 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq591 x
       have i₂ := eq57 sF0 sF2 x
       grind)
    | exact superpose eq57 eq591
    | exact resolve eq591 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq608 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108 eq602
    | exact resolve eq602 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq629 : ∀ X0 : G, (M.op (σ x) X0) ≠ (M.op (σ x) (M.op x y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq588 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 (M.op x y) (σ x)
       have r₂ := eq588
       grind)
    | exact resolve eq12 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : (M.op (σ x) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq587
    | (have j0 := eq587 (σ x) (σ y)
       grind)
    | exact resolve eq587 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq694 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (M.op x y)) ∨ (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq669 eq12
    | (have j0 := eq12 (M.op x y) (σ x)
       grind)
    | exact resolve eq12 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq707 : (k (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq694
       have r₂ := eq588
       grind)
    | exact resolve eq694 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq871 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq607 eq9
    | exact resolve eq9 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) X1) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq607 eq52
    | exact resolve eq52 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq607 eq12
    | exact resolve eq12 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq881 X0
       have i₂ := eq530 sF0 sF0 sF0 sF0
       grind)
    | exact superpose eq530 eq881
    | (have j0 := eq881 X0
       grind)
    | exact resolve eq881 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq933 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) (σ x)) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq584 eq871
    | exact resolve eq871 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq974 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) (σ x)) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq933
  have eq990 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq974
       have i₂ := eq9 sF0 sF0 sF2
       grind)
    | exact superpose eq9 eq974
    | exact resolve eq974 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1191 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq990 eq52
    | exact resolve eq52 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1309 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) ≠ (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (M.op X0 X1) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq225 eq902
    | (have j0 := eq902 (M.op x y)
       grind)
    | exact resolve eq902 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq1327 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (M.op X0 X1) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq1309 X0 X1
       grind)
    | (have r₁ := eq1309 X0 X1
       have r₂ := eq607 (M.op x y)
       grind)
    | exact resolve eq1309 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq1352 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1327
    | (have j0 := eq1327 (σ x) (σ y)
       grind)
    | exact resolve eq1327 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1381 : (M.op (σ x) (M.op x y)) = (k (σ x) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq1352
    | exact resolve eq1352 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1384 : (M.op (σ x) (M.op x y)) = (k (σ x) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1381
  have eq1708 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op (M.op x y) (σ x)) X0) ∨ (M.op (M.op (M.op x y) (σ x)) X0) = (k (σ x) (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq584 eq145
    | (have j0 := eq145 (M.op x y) (σ x) X0
       grind)
    | exact resolve eq145 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq1732 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op x y) X0) = (k x (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq145 x y X0
       have i₂ := eq81 X0 x
       grind)
    | (have i₁ := eq145 x x X0
       have i₂ := eq81 X0 x
       grind)
    | exact superpose eq81 eq145
    | (have j0 := eq145 x y X0
       grind)
    | exact resolve eq145 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1736 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq86 eq145
    | (have j0 := eq145 (σ x) (σ y) X0
       grind)
    | exact resolve eq145 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq1778 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) ≠ (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ (M.op (M.op (M.op x y) (σ x)) X0) = (k (σ x) (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1708 x
       have i₂ := eq57 sF0 sF2 x
       grind)
    | exact superpose eq57 eq1708
    | (have j0 := eq1708 X0
       grind)
    | exact resolve eq1708 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708
  have eq1812 : ∀ X0 : G, (M.op (M.op (M.op x y) (σ x)) X0) = (k (σ x) (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1778 X0
       grind)
    | (have r₁ := eq1778 X0
       have r₂ := eq527 X0 X0
       grind)
    | exact resolve eq1778 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778
  have eq1835 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (k (σ x) (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1812 x
       have i₂ := eq57 sF0 sF2 x
       grind)
    | exact superpose eq57 eq1812
    | exact resolve eq1812 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1812
  have eq1862 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) ≠ (M.op (M.op X3 X4) (M.op X3 X4)) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) = (k (M.op X0 X2) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq146 (M.op X0 X1) X1 X2
       have i₂ := eq52 X0 X1 (M.op X0 X1) X3
       grind)
    | (have i₁ := eq146 (M.op X0 X3) X1 X2
       have i₂ := eq52 X0 X1 (M.op X0 X3) X3
       grind)
    | exact superpose eq52 eq146
    | exact resolve eq146 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1965 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op x y) (M.op x y)) X3) ≠ (M.op (M.op X3 X4) (M.op X3 X4)) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) = (k (M.op X0 X2) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1862 X0 X1 X2 X3 X4
       have i₂ := eq524 X0 X1 (M.op X0 X2) X3
       grind)
    | (have i₁ := eq1862 x y y X3 X4
       have i₂ := eq524 X0 X1 X2 X3
       grind)
    | exact superpose eq524 eq1862
    | (have j0 := eq1862 x y y X3 X4
       grind)
    | exact resolve eq1862 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq1999 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) = (k (M.op X0 X2) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have j0 := eq1965 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq1965 X0 X1 X2 X0 X2
       have r₂ := eq530 X0 X2 X0 X2
       grind)
    | exact resolve eq1965 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1965
  have eq2011 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op x y) (M.op x y)) X3) = (k (M.op X0 X2) (M.op X3 X4)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1999 X0 x X2 X3 X4
       have i₂ := eq524 X0 x (M.op X0 X2) X3
       grind)
    | (have i₁ := eq1999 x y y X3 X4
       have i₂ := eq524 X0 x X2 X3
       grind)
    | exact superpose eq524 eq1999
    | exact resolve eq1999 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq1999
  have eq2172 : (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op x y))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq607 eq1835
    | exact resolve eq1835 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq2179 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (k (σ x) (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq588 eq1835
    | exact resolve eq1835 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2183 : (M.op (σ x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1835 eq1384
    | exact resolve eq1384 eq1835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384 eq1835
  have eq2185 : (M.op (σ x) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2183
  have eq2187 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (k (σ x) (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2179
  have eq2193 : (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op x y))) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq2172
  have eq2197 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (σ x) (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108 eq2187
    | exact resolve eq2187 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2187
  have eq2203 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq225 eq2193
    | exact resolve eq2193 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2225 : (M.op (σ x) (M.op x y)) = (k (σ x) (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq2203
    | exact resolve eq2203 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2203
  have eq2230 : (M.op (σ x) (M.op x y)) = (k (σ x) (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2225
  have eq2239 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2230 eq2197
    | exact resolve eq2197 eq2230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2197 eq2230
  have eq2242 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2239
  have eq2256 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2242 eq9
    | exact resolve eq9 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2285 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X0) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq86 eq2256
    | exact resolve eq2256 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq2310 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq582 eq2285
    | exact resolve eq2285 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2285
  have eq2353 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2310 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq2380 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq108 eq2353
    | exact resolve eq2353 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2434 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ x) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2380 eq225
    | exact resolve eq225 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq2437 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2380 eq608
    | exact resolve eq608 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq2439 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2380 eq229
    | exact resolve eq229 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2472 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq2437
  have eq3019 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2185 eq1191
    | exact resolve eq1191 eq2185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191 eq2185
  have eq3053 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq3019
  have eq3374 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ x) (M.op X2 X3)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2434 eq2434
    | exact resolve eq2434 eq2434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2434
  have eq3495 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ x) (M.op X2 X3)) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq3374 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374
  have eq4229 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq186 (M.op x X0)
       have i₂ := eq81 (M.op x X0) X0
       grind)
    | (have i₁ := eq186 (M.op x y)
       have i₂ := eq81 (M.op x y) x
       grind)
    | exact superpose eq81 eq186
    | exact resolve eq186 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4237 : (σ (M.op (σ x) (M.op x y))) = (M.op (σ (σ x)) (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq588 eq186
    | exact resolve eq186 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq4240 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq186 X0
       grind)
    | exact superpose eq186 eq10
    | exact resolve eq10 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4243 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq186 X0
       grind)
    | exact superpose eq186 eq28
    | exact resolve eq28 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4245 : ∀ X0 : G, (σ (k (M.op X0 X0) x)) = (k (M.op (σ X0) (σ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq30 (M.op X0 X0)
       have i₂ := eq186 X0
       grind)
    | exact superpose eq186 eq30
    | exact resolve eq30 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4246 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 (M.op X0 X0)
       have i₂ := eq186 X0
       grind)
    | exact superpose eq186 eq31
    | exact resolve eq31 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq4263 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq139 eq4229
    | exact resolve eq4229 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4229
  have eq4269 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq4263 X0
       have i₂ := eq186 sF0
       grind)
    | exact superpose eq186 eq4263
    | exact resolve eq4263 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4263
  have eq4274 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq20 eq4269
    | (have j0 := eq4269 X0
       grind)
    | exact resolve eq4269 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4269
  have eq4943 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq326 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq326
    | exact resolve eq326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq6947 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq83 eq873
    | exact resolve eq873 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6962 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (M.op (M.op X0 X2) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq83 eq479
    | exact resolve eq479 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq7299 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (M.op X2 X2)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 X1 (M.op X2 X2) X0
       have i₂ := eq6947 X0 X2
       grind)
    | exact superpose eq6947 eq52
    | exact resolve eq52 eq6947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7317 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq186 (M.op X0 X0)
       have i₂ := eq6947 X0 X0
       grind)
    | exact superpose eq6947 eq186
    | exact resolve eq186 eq6947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6947
  have eq7416 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (σ (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7317 X0
       have i₂ := eq186 X0
       grind)
    | exact superpose eq186 eq7317
    | exact resolve eq7317 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7317
  have eq7471 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) = (σ (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7416 X0
       have i₂ := eq530 (σ X0) (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq530 eq7416
    | exact resolve eq7416 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7416
  have eq8815 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) = (σ (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2380 eq7471
    | exact resolve eq7471 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8817 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (σ (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq94 eq7471
    | exact resolve eq7471 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq8822 : (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2439 eq7471
    | exact resolve eq7471 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq8823 : (σ (M.op (σ x) (M.op x y))) = (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2242 eq7471
    | exact resolve eq7471 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242 eq7471
  have eq8850 : (σ (M.op (σ x) (M.op x y))) = (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq8823
  have eq8851 : (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq8822
  have eq8856 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) = (σ (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8815 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8815
  have eq8861 : (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y))) = (σ (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8850
    | exact resolve eq8850 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8850
  have eq8862 : (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8851
    | exact resolve eq8851 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8851
  have eq8867 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (σ (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8817
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8817
    | exact resolve eq8817 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8817
  have eq8871 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (σ (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108 eq8867
    | exact resolve eq8867 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8867
  have eq8873 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq585 eq8871
    | exact resolve eq8871 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq8874 : (M.op (M.op x y) (σ x)) = (τ (M.op (M.op (σ x) (σ y)) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8871 eq10
    | exact resolve eq10 eq8871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8871
  have eq8883 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq8873
  have eq8885 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8883
       have i₂ := eq186 sF0
       grind)
    | exact superpose eq186 eq8883
    | exact resolve eq8883 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8883
  have eq8887 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8885
    | exact resolve eq8885 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8885
  have eq8902 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8887 eq2472
    | exact resolve eq2472 eq8887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472
  have eq8909 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8887 eq2380
    | exact resolve eq2380 eq8887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8915 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8887 eq108
    | exact resolve eq108 eq8887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8937 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op X0 X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8887 eq7299
    | exact resolve eq7299 eq8887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8887
  have eq8938 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8937 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8937
  have eq8951 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq8909
  have eq8958 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq8902
  have eq8972 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8938 x
       have i₂ := eq530 x x sF1 sF1
       grind)
    | exact superpose eq530 eq8938
    | exact resolve eq8938 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8938
  have eq8980 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108 eq8915
    | exact resolve eq8915 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8915
  have eq8986 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq229 eq8972
    | exact resolve eq8972 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8972
  have eq8990 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq229 eq8980
    | exact resolve eq8980 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq8980
  have eq9007 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8951 eq86
    | exact resolve eq86 eq8951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9013 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8951 eq108
    | exact resolve eq108 eq8951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9067 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108 eq9013
    | exact resolve eq9013 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9013
  have eq9077 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq8990
    | exact resolve eq8990 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9082 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8990 eq2380
    | exact resolve eq2380 eq8990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8990
  have eq9124 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq9082
  have eq9129 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq9077
  have eq9501 : ∀ X0 : G, (σ (M.op (M.op (M.op x y) (M.op x y)) X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq186 (M.op X0 X0)
       have i₂ := eq527 X0 X0
       grind)
    | exact superpose eq527 eq186
    | exact resolve eq186 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq9634 : ∀ X0 : G, (σ (M.op (M.op (M.op x y) (M.op x y)) X0)) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq9501 X0
       have i₂ := eq186 X0
       grind)
    | exact superpose eq186 eq9501
    | exact resolve eq9501 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9501
  have eq9706 : ∀ X0 : G, (σ (M.op (M.op (M.op x y) (M.op x y)) X0)) = (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq9634 X0
       have i₂ := eq530 (σ X0) (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq530 eq9634
    | exact resolve eq9634 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9634
  have eq10015 : ∀ X0 X1 : G, (σ (M.op (M.op (M.op x y) (M.op x y)) X0)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq186 (M.op X0 X1)
       have i₂ := eq530 X0 X1 X0 X1
       grind)
    | (have i₁ := eq186 (M.op (M.op x y) (M.op x y))
       have i₂ := eq530 X0 x (M.op (M.op x y) (M.op x y)) x
       grind)
    | exact superpose eq530 eq186
    | exact resolve eq186 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10063 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (M.op X2 X3)) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq530 eq873
    | exact resolve eq873 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq10174 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq9706 eq10015
    | exact resolve eq10015 eq9706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10015
  have eq10302 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq4274 x
       have i₂ := eq10174 x x
       grind)
    | exact superpose eq10174 eq4274
    | (have j1 := eq10174 x y
       grind)
    | exact resolve eq4274 eq10174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274
  have eq10397 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10302
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10302
    | exact resolve eq10302 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10302
  have eq10417 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq108 eq10397
    | exact resolve eq10397 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10397
  have eq10423 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq10417 eq167
    | (have j0 := eq167 X0 X1
       grind)
    | exact resolve eq167 eq10417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq10518 : (M.op (M.op x y) (σ x)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10417 eq8874
    | exact resolve eq8874 eq10417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8874
  have eq10527 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10417 eq8986
    | exact resolve eq8986 eq10417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8986
  have eq10531 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10417 eq9124
    | exact resolve eq9124 eq10417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9124
  have eq10744 : (M.op (σ x) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9067 eq3053
    | exact resolve eq3053 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10747 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9067 eq2380
    | exact resolve eq2380 eq9067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9067
  have eq10785 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq10747
  have eq10788 : (M.op (σ x) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq10744
  have eq10857 : (M.op (σ x) (M.op x y)) ≠ (M.op (σ x) (M.op x y)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9129 eq629
    | (have j0 := eq629 (M.op x y)
       grind)
    | (have r₁ := eq629 (σ (M.op x y))
       have r₂ := eq9129
       grind)
    | exact resolve eq629 eq9129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10896 : (M.op (σ x) (M.op x y)) ≠ (M.op (σ x) (M.op x y)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq10857
  have eq10897 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq10896
  have eq10898 : (σ (k (M.op x y) x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33 eq10897
    | exact resolve eq10897 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10897
  have eq10912 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ x) (M.op x y)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10531 eq629
    | exact resolve eq629 eq10531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629 eq10531
  have eq10951 : (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ x) (M.op x y)) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq10912
  have eq10965 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10951
       have r₂ := eq8951
       grind)
    | exact resolve eq10951 eq8951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10951
  have eq10969 : (σ (k (M.op x y) x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33 eq10965
    | exact resolve eq10965 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10965
  have eq11412 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (k (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2011 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2011
    | (have j0 := eq2011 x y X0 X1
       grind)
    | exact resolve eq2011 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq11618 : ∀ X0 : G, (σ (M.op (M.op (M.op x y) (M.op x y)) X0)) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | exact superpose eq11412 eq4243
    | exact resolve eq4243 eq11412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq11676 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | exact superpose eq9706 eq11618
    | exact resolve eq11618 eq9706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9706 eq11618
  have eq11887 : (k (M.op x y) x) = (τ (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10898 eq10
    | exact resolve eq10 eq10898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10898
  have eq11905 : (k (M.op x y) x) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10969 eq10
    | exact resolve eq10 eq10969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10969
  have eq11953 : (k (M.op x y) x) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11905 eq10518
    | exact resolve eq10518 eq11905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10518
  have eq11959 : (k (M.op x y) x) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq11953
  have eq12560 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) X0) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10527 eq52
    | exact resolve eq52 eq10527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10527
  have eq12974 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (σ (M.op x y)) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq9007 eq146
    | exact resolve eq146 eq9007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq9007
  have eq13137 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (k (σ (M.op x y)) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq12974 X0 X1
       grind)
    | (have r₁ := eq12974 x x
       have r₂ := eq10063 x x x x
       grind)
    | exact resolve eq12974 eq10063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10063 eq12974
  have eq14615 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13137
    | (have j0 := eq13137 (σ x) (σ y)
       grind)
    | exact resolve eq13137 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13137
  have eq14777 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq14615
    | exact resolve eq14615 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14615
  have eq14781 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq14777
  have eq14783 : (σ (k (M.op x y) x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33 eq14781
    | exact resolve eq14781 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq14781
  have eq14795 : (M.op (σ x) (σ x)) = (σ (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11959 eq14783
    | exact resolve eq14783 eq11959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11959 eq14783
  have eq14816 : (M.op (σ x) (σ x)) = (σ (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq14795
  have eq14853 : (M.op (M.op x y) (σ x)) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14816 eq10
    | exact resolve eq10 eq14816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14816
  have eq18065 : (M.op (σ x) (M.op x y)) = (τ (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8861 eq10
    | exact resolve eq10 eq8861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8861
  have eq18267 : (M.op (σ x) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12560 eq18065
    | exact resolve eq18065 eq12560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12560
  have eq18269 : (M.op (σ x) (M.op x y)) = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq873 eq18065
    | exact resolve eq18065 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18065
  have eq18291 : (M.op (σ x) (M.op x y)) = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq18269
  have eq18293 : (M.op (σ x) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq18267
  have eq18300 : (M.op (σ x) (M.op x y)) = (τ (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10788 eq18291
    | exact resolve eq18291 eq10788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10788
  have eq18301 : (M.op (σ x) (M.op x y)) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10785 eq18291
    | exact resolve eq18291 eq10785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10785
  have eq18303 : (M.op (σ x) (M.op x y)) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2380 eq18291
    | exact resolve eq18291 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18304 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (σ (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18291 eq11
    | exact resolve eq11 eq18291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18291
  have eq18320 : (M.op (σ x) (M.op x y)) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq18303
  have eq18322 : (M.op (σ x) (M.op x y)) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq18301
  have eq18323 : (M.op (σ x) (M.op x y)) = (τ (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq18300
  have eq18332 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (σ (σ x)) (σ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18304 eq4237
    | exact resolve eq4237 eq18304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18304
  have eq18346 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (σ (σ x)) (σ (σ x))) ∨ x = (M.op x y) := by grind
  clear eq18332
  have eq18368 : (M.op (σ x) (σ (M.op x y))) = (σ (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18320 eq11
    | exact resolve eq11 eq18320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18320
  have eq20203 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (σ x)) (σ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18368 eq4237
    | exact resolve eq4237 eq18368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4237 eq18368
  have eq20217 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (σ x)) (σ (σ x))) ∨ x = (M.op x y) := by grind
  clear eq20203
  have eq30049 : (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18346 eq108
    | exact resolve eq108 eq18346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18346
  have eq30138 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30049
       have i₂ := eq9 sF2 sF4 sF1
       grind)
    | exact superpose eq9 eq30049
    | exact resolve eq30049 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30049
  have eq30180 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq528 eq30138
    | exact resolve eq30138 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq30138
  have eq30204 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108 eq30180
    | exact resolve eq30180 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30180
  have eq30213 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10417 eq30204
    | exact resolve eq30204 eq10417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10417 eq30204
  have eq30302 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30213 eq2380
    | exact resolve eq2380 eq30213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30213
  have eq30369 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ x) (σ (σ x))) ∨ x = (M.op x y) := by grind
  clear eq30302
  have eq30437 : (M.op (σ x) (σ x)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30369 eq12
    | exact resolve eq12 eq30369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30369
  have eq30523 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30437
       have r₂ := eq8958
       grind)
    | exact resolve eq30437 eq8958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8958 eq30437
  have eq30539 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (σ x) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq30523
    | exact resolve eq30523 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30523
  have eq30568 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (k (σ x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30539 eq10
    | exact resolve eq10 eq30539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30539
  have eq30592 : (M.op (σ x) (M.op x y)) = (k (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30568 eq18293
    | exact resolve eq18293 eq30568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18293
  have eq30594 : (k (M.op x y) x) = (k (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30568 eq11905
    | exact resolve eq11905 eq30568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11905 eq30568
  have eq30616 : (k (M.op x y) x) = (k (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq30594
  have eq30618 : (M.op (σ x) (M.op x y)) = (k (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq30592
  have eq35564 : (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20217 eq108
    | exact resolve eq108 eq20217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35572 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ (M.op x y))) X0) = (M.op (M.op X0 X1) (σ (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq20217 eq479
    | exact resolve eq479 eq20217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq20217
  have eq35659 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq86 eq35572
    | exact resolve eq35572 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35572
  have eq35665 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108 eq35564
    | exact resolve eq35564 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35564
  have eq35799 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35665 eq2380
    | exact resolve eq2380 eq35665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35665
  have eq35871 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ (σ x))) ∨ x = (M.op x y) := by grind
  clear eq35799
  have eq36077 : (M.op (σ x) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq35871 eq12
    | exact resolve eq12 eq35871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35871
  have eq36181 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq36077
       have r₂ := eq2380 (σ x)
       grind)
    | exact resolve eq36077 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36077
  have eq36216 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (k (σ x) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq36181
    | exact resolve eq36181 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq36181
  have eq36683 : (τ (M.op (M.op (σ x) (σ y)) (σ x))) = (k (σ x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36216 eq10
    | exact resolve eq10 eq36216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37795 : (τ (M.op (σ x) (M.op x y))) = (k (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3053 eq36683
    | exact resolve eq36683 eq3053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36683
  have eq37847 : (τ (M.op (σ x) (M.op x y))) = (k (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq37795
  have eq38540 : (M.op (σ x) (M.op x y)) = (σ (k (σ x) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37847 eq11
    | exact resolve eq11 eq37847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63127 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8862 eq10
    | exact resolve eq10 eq8862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8862
  have eq65122 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq873 eq63127
    | exact resolve eq63127 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq63127
  have eq65157 : (M.op (σ x) (M.op (σ x) (σ y))) = (τ (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq65122
  have eq65207 : (M.op (σ x) (σ x)) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq65157
    | exact resolve eq65157 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65157
  have eq65269 : (M.op (σ x) (σ x)) = (τ (M.op (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq65207
  have eq65806 : (M.op (σ x) (σ x)) = (τ (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9129 eq65269
    | exact resolve eq65269 eq9129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9129 eq65269
  have eq65852 : (M.op (σ x) (σ x)) = (τ (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq65806
  have eq76134 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4240 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4240
    | exact resolve eq4240 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76192 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq4240 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4240
    | (have j0 := eq4240 x
       grind)
    | exact resolve eq4240 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4240
  have eq76262 : (M.op x x) = (M.op (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq76192 eq14853
    | exact resolve eq14853 eq76192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14853
  have eq76263 : (M.op x x) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq76192 eq18322
    | exact resolve eq18322 eq76192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18322 eq76192
  have eq76652 : (k (M.op x y) x) = (τ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq76263 eq11887
    | exact resolve eq11887 eq76263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11887
  have eq76673 : (M.op (σ x) (σ x)) = (τ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq76263 eq65852
    | exact resolve eq65852 eq76263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65852
  have eq76677 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op x x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76263 eq86
    | exact resolve eq86 eq76263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq76263
  have eq76766 : (M.op (σ x) (σ x)) = (τ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq76673
  have eq76787 : (k (M.op x y) x) = (τ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq76652
  have eq76842 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76677 X0
       have i₂ := eq81 X0 x
       grind)
    | exact superpose eq81 eq76677
    | exact resolve eq76677 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76677
  have eq76844 : (M.op (σ x) (σ x)) = (M.op (τ x) (τ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76766
       have i₂ := eq76134 x
       grind)
    | exact superpose eq76134 eq76766
    | exact resolve eq76766 eq76134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76766
  have eq76859 : (k (M.op x y) x) = (M.op (τ x) (τ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq76787
       have i₂ := eq76134 x
       grind)
    | exact superpose eq76134 eq76787
    | exact resolve eq76787 eq76134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76787
  have eq77599 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76842 eq2380
    | exact resolve eq2380 eq76842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77776 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq77599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77599
  have eq79167 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op x x) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq76262 eq52
    | exact resolve eq52 eq76262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76262
  have eq79327 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq79167 X0 X1
       have i₂ := eq81 X1 x
       grind)
    | exact superpose eq81 eq79167
    | exact resolve eq79167 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79167
  have eq80552 : (τ (M.op (σ x) (M.op x y))) = (k (τ (σ x)) (τ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30618 eq4943
    | exact resolve eq4943 eq30618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30618
  have eq80596 : (τ (M.op (σ x) (M.op x y))) = (k (τ (M.op x y)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq590 eq4943
    | exact resolve eq4943 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq80608 : (τ (M.op (σ x) (M.op x y))) = (k (τ (M.op (σ x) (σ y))) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq707 eq4943
    | exact resolve eq4943 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq80674 : (τ (M.op (σ x) (M.op x y))) = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq80608
    | exact resolve eq80608 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80608
  have eq80686 : (τ (M.op (σ x) (M.op x y))) = (k (τ (M.op x y)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq80596
    | exact resolve eq80596 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80596
  have eq80730 : (τ (M.op (σ x) (M.op x y))) = (k x (τ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq80552
    | exact resolve eq80552 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80552
  have eq101035 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X1) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq186 (M.op X0 X0)
       have i₂ := eq6962 X0 X0 X1
       grind)
    | exact superpose eq6962 eq186
    | exact resolve eq186 eq6962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6962
  have eq101354 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) = (σ (M.op (M.op X0 X1) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq101035 X0 X1
       have i₂ := eq10174 X0 X0
       grind)
    | exact superpose eq10174 eq101035
    | exact resolve eq101035 eq10174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10174 eq101035
  have eq104334 : (k (σ x) x) = (k (τ (M.op x y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80686 eq37847
    | exact resolve eq37847 eq80686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104371 : (k (σ x) x) = (k (τ (M.op x y)) x) ∨ x = (M.op x y) := by grind
  clear eq104334
  have eq106973 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (σ (k (M.op X0 X0) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4245 eq589
    | exact resolve eq589 eq4245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq4245
  have eq108159 : (σ (k (σ x) x)) = (k (M.op x y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104371 eq49
    | exact resolve eq49 eq104371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104371
  have eq108203 : (k (M.op x y) (σ x)) = (σ (k (σ x) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108159
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108159
    | exact resolve eq108159 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108159
  have eq114472 : ∀ X0 : G, (τ (M.op (M.op (M.op x y) (M.op x y)) (σ X0))) = (k (τ (σ (M.op x y))) (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | exact superpose eq11676 eq4943
    | exact resolve eq4943 eq11676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11676
  have eq114473 : ∀ X0 : G, (τ (M.op (M.op (M.op x y) (M.op x y)) (σ X0))) = (k (τ (σ (M.op x y))) (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq114472 X0
       have i₂ := eq76134 (σ X0)
       grind)
    | exact superpose eq76134 eq114472
    | exact resolve eq114472 eq76134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114472
  have eq114568 : ∀ X0 : G, (τ (M.op (M.op (M.op x y) (M.op x y)) (σ X0))) = (k (τ (σ (M.op x y))) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114473 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq114473
    | exact resolve eq114473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114473
  have eq114620 : ∀ X0 : G, (k (M.op x y) (M.op X0 X0)) = (τ (M.op (M.op (M.op x y) (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq114568
    | exact resolve eq114568 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq114568
  have eq114652 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (τ (M.op (M.op (M.op x y) (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq11412 eq114620
    | exact resolve eq114620 eq11412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11412 eq114620
  have eq119472 : (M.op (M.op x y) (τ x)) = (M.op (k (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92 (τ x) (τ x)
       have i₂ := eq76859
       grind)
    | exact superpose eq76859 eq92
    | exact resolve eq92 eq76859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76859
  have eq141085 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (τ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108 (τ x) (τ x)
       have i₂ := eq76844
       grind)
    | exact superpose eq76844 eq108
    | exact resolve eq108 eq76844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76844
  have eq141234 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (τ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108 eq141085
    | exact resolve eq141085 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141085
  have eq141399 : (M.op (σ x) (σ x)) = (M.op (σ x) (τ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq141234
    | exact resolve eq141234 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141234
  have eq141533 : (M.op (σ x) (σ x)) = (M.op (σ x) (τ x)) ∨ x = (M.op x y) := by grind
  clear eq141399
  have eq142380 : (M.op (σ x) (σ x)) = (M.op (M.op x y) (τ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq141533 eq77776
    | exact resolve eq77776 eq141533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141533
  have eq142492 : (M.op (σ x) (σ x)) = (M.op (M.op x y) (τ x)) ∨ x = (M.op x y) := by grind
  clear eq142380
  have eq155732 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) ≠ (M.op (σ x) (M.op x y)) ∨ (M.op (σ x) (M.op x y)) = (k (σ x) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3053 eq10423
    | exact resolve eq10423 eq3053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3053 eq10423
  have eq155755 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (k (σ x) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq155732 X0
       grind)
    | (have r₁ := eq155732 X0
       have r₂ := eq8951
       grind)
    | exact resolve eq155732 eq8951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8951 eq155732
  have eq156981 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq155755
    | (have j0 := eq155755 (σ y)
       grind)
    | exact resolve eq155755 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155755
  have eq157169 : (τ (M.op (σ x) (M.op x y))) = (k (τ (σ x)) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq156981 eq4943
    | exact resolve eq4943 eq156981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156981
  have eq157180 : (τ (M.op (σ x) (M.op x y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq157169
    | exact resolve eq157169 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157169
  have eq157204 : (τ (M.op (M.op x y) (M.op x y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq77776 eq157180
    | exact resolve eq157180 eq77776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157294 : (τ (M.op (M.op x y) (M.op x y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq157204
  have eq157313 : (M.op (τ (M.op x y)) (τ (M.op x y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq157294
       have i₂ := eq76134 sF0
       grind)
    | exact superpose eq76134 eq157294
    | exact resolve eq157294 eq76134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157294
  have eq195383 : (k (σ x) x) = (k x (τ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80730 eq37847
    | exact resolve eq37847 eq80730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37847 eq80730
  have eq195468 : (k (σ x) x) = (k x (τ x)) ∨ x = (M.op x y) := by grind
  clear eq195383
  have eq196310 : (σ (k (σ x) x)) = (k (σ x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48 x x
       have i₂ := eq195468
       grind)
    | exact superpose eq195468 eq48
    | exact resolve eq48 eq195468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195468
  have eq196393 : (k (σ x) x) = (σ (k (σ x) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq196310
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq196310
    | exact resolve eq196310 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196310
  have eq197261 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196393 eq36216
    | exact resolve eq36216 eq196393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197267 : (k (M.op x y) (σ x)) = (k (σ x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196393 eq108203
    | exact resolve eq108203 eq196393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108203
  have eq197311 : (k (M.op x y) (σ x)) = (k (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq197267
  have eq197317 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (σ x) x) ∨ x = (M.op x y) := by grind
  clear eq197261
  have eq197517 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (k (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq197311 eq36216
    | exact resolve eq36216 eq197311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36216
  have eq197534 : (k (M.op x y) (σ x)) = (σ (k (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq197311 eq196393
    | exact resolve eq196393 eq197311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196393 eq197311
  have eq197551 : (k (M.op x y) (σ x)) = (σ (k (M.op x y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq197534
  have eq197568 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (k (M.op x y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq197517
  have eq199378 : (k (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq197317 eq30616
    | exact resolve eq30616 eq197317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30616
  have eq199389 : (M.op (σ x) (M.op x y)) = (σ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq197317 eq38540
    | exact resolve eq38540 eq197317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38540 eq197317
  have eq199434 : (M.op (σ x) (M.op x y)) = (σ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq199389
  have eq199445 : (k (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq199378
  have eq208361 : (M.op (M.op (σ x) (σ y)) (σ x)) = (τ (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq199434 eq10
    | exact resolve eq10 eq199434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199434
  have eq221932 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq208361 eq80674
    | exact resolve eq80674 eq208361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208361
  have eq222023 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op x y) := by grind
  clear eq221932
  have eq235811 : (σ (M.op (M.op (σ x) (σ y)) (σ x))) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq222023 eq49
    | exact resolve eq49 eq222023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222023
  have eq235871 : (k (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq235811
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq235811
    | exact resolve eq235811 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235811
  have eq396083 : ∀ X0 : G, (M.op (M.op x y) X0) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (M.op x y) X0) = (k x (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1732 X0
       have i₂ := eq7299 X0 X0 X0
       grind)
    | exact superpose eq7299 eq1732
    | (have j0 := eq1732 X0
       grind)
    | exact resolve eq1732 eq7299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1732
  have eq396100 : ∀ X0 : G, (M.op (M.op x y) X0) = (k x (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq396083 X0
       grind)
    | (have r₁ := eq396083 X0
       have r₂ := eq76842 X0
       grind)
    | exact resolve eq396083 eq76842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76842 eq396083
  have eq396144 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (σ x) (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1736 X0
       have i₂ := eq7299 X0 X0 X0
       grind)
    | exact superpose eq7299 eq1736
    | (have j0 := eq1736 X0
       grind)
    | (have r₁ := eq1736 x
       have r₂ := eq7299 x x x
       grind)
    | exact resolve eq1736 eq7299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1736
  have eq396158 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k (σ x) (M.op X0 X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq396144 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396144
  have eq396181 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 X0)) = (k x (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq396100 (M.op X0 X0)
       have i₂ := eq7299 X0 X0 X0
       grind)
    | exact superpose eq7299 eq396100
    | exact resolve eq396100 eq7299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396345 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 X0)) = (k x (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq396181 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396181
  have eq396382 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k x (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq139 eq396345
    | exact resolve eq396345 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq396345
  have eq396542 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (M.op (M.op (σ x) (σ y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq396158 eq4246
    | exact resolve eq4246 eq396158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4246 eq396158
  have eq396834 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k x (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2380 eq396382
    | exact resolve eq396382 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396382
  have eq396893 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k x (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq396834 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396834
  have eq397225 : (M.op (M.op x y) (M.op x y)) = (k x (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq396893
    | (have j0 := eq396893 (σ y)
       grind)
    | exact resolve eq396893 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396893
  have eq397355 : (M.op (M.op x y) (M.op x y)) = (k x (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq397225
    | exact resolve eq397225 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397225
  have eq397358 : (M.op (M.op x y) (M.op x y)) = (k x (σ x)) ∨ x = (M.op x y) := by grind
  clear eq397355
  have eq397361 : (τ (M.op (M.op x y) (M.op x y))) = (k (τ x) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq397358 eq4943
    | exact resolve eq4943 eq397358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397358
  have eq397364 : (τ (M.op (M.op x y) (M.op x y))) = (k (τ x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq397361
    | exact resolve eq397361 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397361
  have eq397365 : (M.op (τ (M.op x y)) (τ (M.op x y))) = (k (τ x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq397364
       have i₂ := eq76134 sF0
       grind)
    | exact superpose eq76134 eq397364
    | exact resolve eq397364 eq76134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397364
  have eq562631 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (σ (k (M.op (M.op (σ x) (σ y)) X0) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq106973 (M.op X0 X0)
       have i₂ := eq7299 X0 X0 X0
       grind)
    | exact superpose eq7299 eq106973
    | exact resolve eq106973 eq7299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562733 : ∀ X0 : G, (k (M.op X0 X0) x) = (τ (M.op (σ x) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (k (M.op X0 X0) x)
       have i₂ := eq106973 X0
       grind)
    | exact superpose eq106973 eq10
    | exact resolve eq10 eq106973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106973
  have eq562822 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (σ (k (M.op (M.op (σ x) (σ y)) X0) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq562631 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562631
  have eq562937 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (k (M.op X0 X0) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq562733 eq18323
    | exact resolve eq18323 eq562733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18323 eq562733
  have eq563011 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (k (M.op X0 X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq562937 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562937
  have eq564630 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (k (M.op (M.op (σ x) (σ y)) X0) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq563011 (M.op X0 X0)
       have i₂ := eq7299 X0 X0 X0
       grind)
    | exact superpose eq7299 eq563011
    | exact resolve eq563011 eq7299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7299 eq563011
  have eq564832 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (k (M.op (M.op (σ x) (σ y)) X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq564630 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564630
  have eq565147 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (k (M.op (σ x) X0) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2380 eq564832
    | exact resolve eq564832 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564832
  have eq565209 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (k (M.op (σ x) X0) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq565147 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565147
  have eq565757 : (M.op (σ x) (M.op x y)) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq565209
    | (have j0 := eq565209 (σ y)
       grind)
    | exact resolve eq565209 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565209
  have eq567477 : (τ (M.op (σ x) (M.op x y))) = (k (τ (M.op (σ x) (σ y))) (τ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq565757 eq4943
    | exact resolve eq4943 eq565757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565757
  have eq661328 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (σ (k (M.op (σ x) X0) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2380 eq562822
    | exact resolve eq562822 eq2380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562822
  have eq661489 : ∀ X0 : G, (M.op (σ x) (M.op x y)) = (σ (k (M.op (σ x) X0) x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq661328 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661328
  have eq666796 : (M.op (σ x) (M.op x y)) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq661489
    | (have j0 := eq661489 (σ y)
       grind)
    | exact resolve eq661489 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661489
  have eq667151 : (τ (M.op (σ x) (M.op x y))) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq666796 eq10
    | exact resolve eq10 eq666796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666796
  have eq667190 : (τ (M.op (M.op x y) (M.op x y))) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq77776 eq667151
    | exact resolve eq667151 eq77776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667242 : (k (τ (M.op (σ x) (σ y))) x) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq667151 eq80674
    | exact resolve eq80674 eq667151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80674
  have eq667243 : (k (τ (M.op x y)) x) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq667151 eq80686
    | exact resolve eq80686 eq667151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80686
  have eq667252 : (k x (τ (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq667151 eq157180
    | exact resolve eq157180 eq667151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157180
  have eq667301 : (k x (τ (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) := by grind
  clear eq667252
  have eq667310 : (k (τ (M.op x y)) x) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) := by grind
  clear eq667243
  have eq667311 : (k (τ (M.op (σ x) (σ y))) x) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) := by grind
  clear eq667242
  have eq667363 : (τ (M.op (M.op x y) (M.op x y))) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) := by grind
  clear eq667190
  have eq667371 : (M.op (τ (M.op x y)) (τ (M.op x y))) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq667363
       have i₂ := eq76134 sF0
       grind)
    | exact superpose eq76134 eq667363
    | exact resolve eq667363 eq76134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76134 eq667363
  have eq667450 : (k (M.op x y) (σ x)) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq667310 eq49
    | exact resolve eq49 eq667310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667310
  have eq667528 : (k (M.op x y) (σ x)) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq667450
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq667450
    | exact resolve eq667450 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667450
  have eq667612 : (k (M.op (σ x) (σ y)) (σ x)) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq667311 eq49
    | exact resolve eq49 eq667311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667311
  have eq667701 : (k (M.op (σ x) (σ y)) (σ x)) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq667612
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq667612
    | exact resolve eq667612 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667612
  have eq667775 : (k (σ x) (M.op (σ x) (σ y))) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq667301 eq48
    | exact resolve eq48 eq667301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq667301
  have eq667874 : (k (σ x) (M.op (σ x) (σ y))) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq667775
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq667775
    | exact resolve eq667775 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667775
  have eq668004 : (σ (M.op (M.op (σ x) (σ y)) (σ x))) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq667701 eq235871
    | exact resolve eq235871 eq667701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235871 eq667701
  have eq668047 : (σ (M.op (M.op (σ x) (σ y)) (σ x))) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by grind
  clear eq668004
  have eq729648 : (k (τ x) x) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq397365 eq667371
    | exact resolve eq667371 eq397365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397365 eq667371
  have eq729790 : (k (τ x) x) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) := by grind
  clear eq729648
  have eq729844 : (σ (k (M.op (σ x) (σ y)) x)) = (k x (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49 x x
       have i₂ := eq729790
       grind)
    | exact superpose eq729790 eq49
    | exact resolve eq49 eq729790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729790
  have eq729851 : (k x (σ x)) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq729844
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq729844
    | exact resolve eq729844 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729844
  have eq729911 : (k (M.op x y) (σ x)) = (k x (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq729851 eq667528
    | exact resolve eq667528 eq729851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667528
  have eq729921 : (k x (σ x)) = (σ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq729851 eq668047
    | exact resolve eq668047 eq729851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668047 eq729851
  have eq729967 : (k x (σ x)) = (σ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq729921
  have eq729977 : (k (M.op x y) (σ x)) = (k x (σ x)) ∨ x = (M.op x y) := by grind
  clear eq729911
  have eq730370 : (k x (σ x)) = (σ (k x (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq729977 eq197551
    | exact resolve eq197551 eq729977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197551
  have eq730376 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (k x (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq729977 eq197568
    | exact resolve eq197568 eq729977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197568 eq729977
  have eq730541 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (k x (σ x))) ∨ x = (M.op x y) := by grind
  clear eq730376
  have eq730547 : (k x (σ x)) = (σ (k x (σ x))) ∨ x = (M.op x y) := by grind
  clear eq730370
  have eq736494 : (k x (σ x)) = (τ (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq730541 eq10
    | exact resolve eq10 eq730541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730541
  have eq867519 : (M.op (σ x) (σ x)) = (M.op (k (M.op x y) x) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq119472 eq142492
    | exact resolve eq142492 eq119472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119472 eq142492
  have eq867542 : (M.op (σ x) (σ x)) = (M.op (k (M.op x y) x) x) ∨ x = (M.op x y) := by grind
  clear eq867519
  have eq871326 : (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (M.op (σ x) (σ y)) (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq867542 eq108
    | exact resolve eq108 eq867542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867542
  have eq871411 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq108 eq871326
    | exact resolve eq871326 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq871326
  have eq871470 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (k (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq871411 eq2380
    | exact resolve eq2380 eq871411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380 eq871411
  have eq871636 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (k (M.op x y) x)) ∨ x = (M.op x y) := by grind
  clear eq871470
  have eq872111 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq199445 eq871636
    | exact resolve eq871636 eq199445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199445 eq871636
  have eq872341 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq872111
  have eq872445 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op X0 X1)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq872341 eq3495
    | exact resolve eq3495 eq872341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3495 eq872341
  have eq872637 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op X0 X1)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq872445 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872445
  have eq874440 : ∀ X0 X1 : G, (k x (σ x)) = (τ (M.op (σ x) (M.op X0 X1))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq872637 eq736494
    | exact resolve eq736494 eq872637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736494 eq872637
  have eq874665 : ∀ X0 X1 : G, (k x (σ x)) = (τ (M.op (σ x) (M.op X0 X1))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq874440 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874440
  have eq1238917 : (k (M.op (σ x) (σ y)) x) = (k (τ (M.op (σ x) (σ y))) (τ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq567477 eq667151
    | exact resolve eq667151 eq567477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567477 eq667151
  have eq1238937 : (k (M.op (σ x) (σ y)) x) = (k (τ (M.op (σ x) (σ y))) (τ x)) ∨ x = (M.op x y) := by grind
  clear eq1238917
  have eq1239072 : (k (M.op (σ x) (σ y)) (σ (τ x))) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1238937 eq49
    | exact resolve eq49 eq1238937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1238937
  have eq1239106 : (k (M.op (σ x) (σ y)) x) = (σ (k (M.op (σ x) (σ y)) x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1239072
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq1239072
    | exact resolve eq1239072 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239072
  have eq1239180 : (k (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1239106 eq667874
    | exact resolve eq667874 eq1239106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667874
  have eq1239252 : (k (σ x) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) x) ∨ x = (M.op x y) := by grind
  clear eq1239180
  have eq1239591 : (k (σ x) (M.op (σ x) (σ y))) = (σ (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1239252 eq1239106
    | exact resolve eq1239106 eq1239252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239106 eq1239252
  have eq1239593 : (k (σ x) (M.op (σ x) (σ y))) = (σ (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq1239591
  have eq1240941 : (k (σ x) (M.op (σ x) (σ y))) = (τ (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1239593 eq10
    | exact resolve eq10 eq1239593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239593
  have eq1241030 : (k (σ x) (M.op (σ x) (σ y))) = (k (τ (σ x)) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1240941
       have i₂ := eq4943 sF2 sF4
       grind)
    | exact superpose eq4943 eq1240941
    | exact resolve eq1240941 eq4943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4943 eq1240941
  have eq1241036 : (k (σ x) (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq1241030
    | exact resolve eq1241030 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241030
  have eq1245291 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1241036 eq157313
    | exact resolve eq157313 eq1241036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157313 eq1241036
  have eq1245386 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (τ (M.op x y)) (τ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1245291
  have eq2492582 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (σ (k x (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq874665 eq11
    | exact resolve eq11 eq874665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874665
  have eq2882909 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (k x (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2492582 eq730547
    | exact resolve eq730547 eq2492582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730547 eq2492582
  have eq2882917 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (k x (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq2882909 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882909
  have eq2883354 : (k x (σ x)) = (M.op (σ x) (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1245386 eq2882917
    | exact resolve eq2882917 eq1245386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245386 eq2882917
  have eq2885322 : (k x (σ x)) = (M.op (σ x) (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq2883354
  have eq2886147 : (k x (σ x)) = (M.op (M.op x y) (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2885322 eq77776
    | exact resolve eq77776 eq2885322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77776 eq2885322
  have eq2886308 : (k x (σ x)) = (M.op (M.op x y) (k (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq2886147
  have eq3094552 : ∀ X0 : G, (k x (M.op X0 X0)) = (τ (M.op (M.op (σ x) (σ y)) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (k x (M.op X0 X0))
       have i₂ := eq396542 X0
       grind)
    | exact superpose eq396542 eq10
    | exact resolve eq10 eq396542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396542
  have eq3102289 : (σ (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) (σ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8856
    | (have j0 := eq8856 (σ y)
       grind)
    | exact resolve eq8856 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8856
  have eq3102292 : (M.op (σ x) (σ y)) = (τ (M.op (M.op (M.op x y) (M.op x y)) (σ (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3102289 eq10
    | exact resolve eq10 eq3102289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3102289
  have eq3102293 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114652 eq3102292
    | exact resolve eq3102292 eq114652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114652 eq3102292
  have eq3102316 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3102293 eq52
    | exact resolve eq52 eq3102293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq3102293
  have eq3103126 : (M.op (σ x) (σ y)) = (M.op (k x (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2886308 eq3102316
    | exact resolve eq3102316 eq2886308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2886308 eq3102316
  have eq3103371 : (M.op (σ x) (σ y)) = (M.op (k x (σ x)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3103126
  have eq3103947 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (M.op (σ x) (σ y)) (σ x))) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq729967 eq3103371
    | exact resolve eq3103371 eq729967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729967 eq3103371
  have eq3104105 : (M.op (σ x) (σ y)) = (M.op (σ (M.op (M.op (σ x) (σ y)) (σ x))) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3103947
  have eq3104364 : (σ x) = (M.op (σ (M.op (σ x) (σ x))) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq582 eq3104105
    | exact resolve eq3104105 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq3104105
  have eq3104561 : (σ x) = (M.op (σ (M.op (σ x) (σ x))) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3104364
  have eq3104580 : (σ x) = (M.op (M.op (σ (σ x)) (σ (σ x))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3104561
       have i₂ := eq186 sF2
       grind)
    | exact superpose eq186 eq3104561
    | exact resolve eq3104561 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq3104561
  have eq3104592 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3104580
       have i₂ := eq9 (σ sF2) sF3 x
       grind)
    | (have i₁ := eq3104580
       have i₂ := eq9 sF3 (σ sF2) (σ sF2)
       grind)
    | exact superpose eq9 eq3104580
    | exact resolve eq3104580 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3104580
  have eq3105938 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3104592 eq35659
    | exact resolve eq35659 eq3104592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35659 eq3104592
  have eq3106053 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3105938
  have eq3108255 : (k x (M.op y y)) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3094552 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3094552
    | (have j0 := eq3094552 y
       grind)
    | exact resolve eq3094552 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3094552
  have eq3108261 : (τ (σ x)) = (k x (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3106053 eq3108255
    | exact resolve eq3108255 eq3106053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3106053 eq3108255
  have eq3108265 : (τ (σ x)) = (k x (M.op y y)) ∨ x = (M.op x y) := by grind
  clear eq3108261
  have eq3108266 : x = (k x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq3108265
    | exact resolve eq3108265 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq3108265
  have eq3108270 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq396100 y
       have i₂ := eq3108266
       grind)
    | exact superpose eq3108266 eq396100
    | exact resolve eq396100 eq3108266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396100 eq3108266
  have eq3108272 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq3108270
  have eq3108307 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3108272 eq79327
    | exact resolve eq79327 eq3108272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79327
  have eq3108755 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3108307 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108307
  have eq3118883 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3108755 eq3108272
    | exact resolve eq3108272 eq3108755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108272 eq3108755
  have eq3118990 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3118883
  have eq3119130 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3118990
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3118990
    | exact resolve eq3118990 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118990
  have eq3119131 : x = (M.op x y) := by grind
  clear eq3119130
  have eq3119175 : x = (M.op x y) := by
    first
    | exact superpose eq3119131 eq18
    | exact resolve eq18 eq3119131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3119176 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3119131 eq20
    | exact resolve eq20 eq3119131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3119184 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq3119131 eq81
    | exact resolve eq81 eq3119131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq3119186 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | exact superpose eq3119131 eq92
    | exact resolve eq92 eq3119131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq3120382 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) x)) = (M.op (M.op x x) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq3119131 eq101354
    | exact resolve eq101354 eq3119131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101354 eq3119131
  have eq3127961 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op x x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3120382 X0 x
       have i₂ := eq3119186 X0 x
       grind)
    | exact superpose eq3119186 eq3120382
    | exact resolve eq3120382 eq3119186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119186 eq3120382
  have eq3128201 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3119176
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3119176
    | exact resolve eq3119176 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119176
  have eq3128789 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3127961 X0
       have i₂ := eq3119184 (σ X0) x
       grind)
    | exact superpose eq3119184 eq3127961
    | exact resolve eq3127961 eq3119184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3127961
  have eq3128899 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3128201 eq22
    | exact resolve eq22 eq3128201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq3128900 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3128201 eq26
    | exact resolve eq26 eq3128201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3128201
  have eq3143344 : (σ x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq3128789 y
       have i₂ := eq3119175
       grind)
    | exact superpose eq3119175 eq3128789
    | exact resolve eq3128789 eq3119175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119175 eq3128789
  have eq3143749 : (σ x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq3143344
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3143344
    | exact resolve eq3143344 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3143344
  have eq3143789 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq3143749
       have i₂ := eq3128899
       grind)
    | exact superpose eq3128899 eq3143749
    | exact resolve eq3143749 eq3128899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3128899 eq3143749
  have eq3143873 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq3143789 eq3119184
    | exact resolve eq3119184 eq3143789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119184
  have eq3144020 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq3143873 eq3128900
    | exact resolve eq3128900 eq3143873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3128900 eq3143873
  have eq3144025 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3143789 eq3144020
    | exact resolve eq3144020 eq3143789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3143789 eq3144020
  have eq3144089 : False := by grind
  exact eq3144089

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_y_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X0 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X2 X0 X2
       have i₂ := eq14 X0 X2 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X3) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X2 X2) (M.op X2 X2)) ∨ (M.op (M.op X0 X1) X2) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X1) X2) ∨ (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X2) (M.op X2 X2)) ∨ (M.op X2 X2) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq12 X0 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op X2 X2)
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X2) (M.op X1 X2))
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq92
    | (have j0 := eq92 (σ X0) (σ X1)
       grind)
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq92 y x
       grind)
    | exact superpose eq92 eq98
    | (have j1 := eq92 y x
       grind)
    | exact resolve eq98 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq130 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq132 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq130
    | exact resolve eq130 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq133 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq132
    | exact resolve eq132 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq133 eq92
    | (have j0 := eq92 (σ y) (σ x)
       grind)
    | exact resolve eq92 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq202
    | exact resolve eq202 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq206 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq203
       have r₂ := eq27
       grind)
    | exact resolve eq203 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq208 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq206
    | exact resolve eq206 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq210 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq208 eq27
    | exact resolve eq27 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq53 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq54 eq262
    | exact resolve eq262 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : (M.op (M.op x y) (σ x)) = (M.op (σ x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq208 eq432
    | exact resolve eq432 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq456 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op x y) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq452 eq14
    | exact resolve eq14 eq452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452
  have eq457 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) (σ x)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq54 eq456
    | exact resolve eq456 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq456
  have eq494 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X2 X2) X0 X3 X4
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X2) X0 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X0 X0) x X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq516 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) X1) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq457 eq51
    | exact resolve eq51 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq843 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X4 X4) X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X4 X2 X0 X3
       have i₂ := eq51 X0 X0 (M.op X2 X3) X1
       grind)
    | (have i₁ := eq56 X4 X2 X0 X3
       have i₂ := eq51 X0 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq56
  have eq1180 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq115 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1634 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1635 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (k X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1634 X0 X1
       have j1 := eq69 X0 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq1634 X0 X1
       have r₂ := eq69 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq1634 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1634
  have eq11499 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq494 X0 X1 X2 X3 x
       have i₂ := eq498 X2 X3 x
       grind)
    | exact superpose eq498 eq494
    | exact resolve eq494 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq498
  have eq16579 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) X2) X0) = (M.op (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq843 X0 X1 X2 X3 x
       have i₂ := eq11499 x x X2 X0
       grind)
    | exact superpose eq11499 eq843
    | exact resolve eq843 eq11499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq11499
  have eq23639 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) X0) = (k X0 (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq1635 (M.op x y) x
       have i₂ := eq16579 (M.op (M.op x y) x) x x x
       grind)
    | (have i₁ := eq1635 x x
       have i₂ := eq16579 x x x x
       grind)
    | exact superpose eq16579 eq1635
    | exact resolve eq1635 eq16579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635 eq16579
  have eq23657 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (M.op (σ x) (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq516 eq23639
    | exact resolve eq23639 eq516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq23735 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq208 eq23657
    | exact resolve eq23657 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23657
  have eq23863 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23735 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23735
  have eq23970 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq23863
    | (have j0 := eq23863 (σ y)
       grind)
    | exact resolve eq23863 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23863
  have eq24059 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq208 eq23970
    | exact resolve eq23970 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq23970
  have eq24066 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq24059
  have eq24151 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24066 eq133
    | exact resolve eq133 eq24066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq24066
  have eq24157 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq24151
  have eq24162 : x = (M.op x y) := by
    first
    | (have r₁ := eq24157
       have r₂ := eq210
       grind)
    | exact resolve eq24157 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq24157
  have eq24165 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq24162 eq20
    | exact resolve eq20 eq24162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq24185 : ∀ X0 : G, (M.op (M.op x X0) X0) = (k X0 (M.op (M.op x X0) X0)) := by
    intro X0
    first
    | exact superpose eq24162 eq23639
    | exact resolve eq23639 eq24162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23639
  have eq24187 : ∀ X0 : G, (M.op (M.op x y) X0) = (k X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq24185 x
       have i₂ := eq262 x x
       grind)
    | (have i₁ := eq24185 y
       have i₂ := eq262 X0 y
       grind)
    | exact superpose eq262 eq24185
    | exact resolve eq24185 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq24185
  have eq24201 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq24165
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24165
    | exact resolve eq24165 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24165
  have eq24202 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq24162 eq24187
    | exact resolve eq24187 eq24162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24187
  have eq24481 : (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq24202 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24202
    | (have j0 := eq24202 y
       grind)
    | exact resolve eq24202 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq24202
  have eq24504 : x = (k y x) := by
    first
    | exact superpose eq24162 eq24481
    | exact resolve eq24481 eq24162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24162 eq24481
  have eq24509 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1180 x y
       have i₂ := eq24504
       grind)
    | exact superpose eq24504 eq1180
    | (have j0 := eq1180 x y
       grind)
    | exact resolve eq1180 eq24504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq24504
  have eq24512 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq24509
  have eq24517 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24512
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24512
    | exact resolve eq24512 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq24512
  have eq24520 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24517
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24517
    | exact resolve eq24517 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq24517
  have eq24522 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24520
    | exact resolve eq24520 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq24520
  have eq24524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24201 eq24522
    | exact resolve eq24522 eq24201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24201 eq24522
  have eq24525 : False := by grind
  exact eq24525
