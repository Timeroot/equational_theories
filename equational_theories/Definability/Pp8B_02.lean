import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pyx_y_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq14 X0 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (M.op (M.op X0 (M.op X1 X0)) X1) = (M.op X2 X2) ∨ (k (M.op (M.op X0 (M.op X1 X0)) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op (M.op X0 (M.op X1 X0)) X1) X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 (M.op X2 X1)) X2) X1
       have r₂ := eq14 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 (M.op X1 X0)) X1) X2) = X2 ∨ (M.op (M.op X0 (M.op X1 X0)) X1) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq76 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq87 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq111
    | exact resolve eq111 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq237 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq326 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  have eq652 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) ∨ (M.op (M.op X1 (M.op X2 X1)) X2) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have i₂ := eq77 X1 X2 (τ X0)
       grind)
    | exact superpose eq77 eq39
    | (have j1 := eq77 X1 X2 (τ X0)
       grind)
    | exact resolve eq39 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq77
  have eq655 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X1)) X2) = (M.op (τ X0) (τ X0)) ∨ (k (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq652 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq652
    | (have j0 := eq652 X0 X1 X2
       grind)
    | exact resolve eq652 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq868 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq93 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq869 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq868 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq5138 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq869 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq869
    | (have j0 := eq869 (τ X0)
       grind)
    | exact resolve eq869 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq5148 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5138 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5138
    | (have j0 := eq5138 X0
       grind)
    | exact resolve eq5138 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5138
  have eq5154 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5148 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5148
    | (have j0 := eq5148 X0
       grind)
    | exact resolve eq5148 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5148
  have eq26320 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = (σ (M.op (τ X2) (M.op (M.op X0 (M.op X1 X0)) X1))) ∨ (k (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq326 X0
       have i₂ := eq655 X0 X1 X2
       grind)
    | exact superpose eq655 eq326
    | (have j1 := eq655 X2 X0 X1
       grind)
    | exact resolve eq326 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq655
  have eq26382 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = (σ (τ X2)) ∨ (k (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26320 X0 X1 X2
       have i₂ := eq14 (τ X2) X0 X1
       grind)
    | exact superpose eq14 eq26320
    | (have j0 := eq26320 X0 X1 X2
       grind)
    | exact resolve eq26320 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26320
  have eq26456 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 ∨ (k (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26382 X0 X1 X2
       have i₂ := eq15 X2
       grind)
    | exact superpose eq15 eq26382
    | (have j0 := eq26382 X0 X1 X2
       grind)
    | exact resolve eq26382 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26382
  have eq26457 : ∀ X0 X1 X2 : G, (k (σ (M.op (M.op X0 (M.op X1 X0)) X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq26456 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26456
  have eq26639 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ (M.op (M.op X1 (M.op X2 X1)) X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq237 (σ (M.op (M.op X1 (M.op X2 X1)) X2)) X0
       have i₂ := eq26457 X1 X2 (σ X0)
       grind)
    | exact superpose eq26457 eq237
    | exact resolve eq237 eq26457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq26683 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26639 X0 X1 X2
       have i₂ := eq16 (M.op (M.op X1 (M.op X2 X1)) X2)
       grind)
    | exact superpose eq16 eq26639
    | exact resolve eq26639 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26639
  have eq26696 : ∀ X0 X1 X2 : G, (k (M.op (M.op X1 (M.op X2 X1)) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26683 X0 X1 X2
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq26683
    | exact resolve eq26683 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26683
  have eq51938 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51945 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq51938
    | exact resolve eq51938 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51938
  have eq51956 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq51945
       have r₂ := eq28
       grind)
    | exact resolve eq51945 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51945
  have eq51959 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  have eq52014 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq51959 eq87
    | exact resolve eq87 eq51959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51959
  have eq52512 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq51956 eq52014
    | exact resolve eq52014 eq51956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51956 eq52014
  have eq52563 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq52512
  have eq52571 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq52563
    | exact resolve eq52563 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52563
  have eq52572 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq5154 y
       grind)
    | (have r₁ := eq52571
       have r₂ := eq5154 y
       grind)
    | exact resolve eq52571 eq5154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154 eq52571
  have eq52575 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq52572
  have eq52678 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq52575
    | exact resolve eq52575 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52575
  have eq52696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq52678 eq112
    | exact resolve eq112 eq52678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq52678
  have eq52710 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq52696
  have eq52712 : y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq52710
       have r₂ := eq28
       grind)
    | exact resolve eq52710 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52710
  have eq53084 : (k y y) = (M.op y y) ∨ y = (M.op x x) := by grind
  have eq53085 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq52712
       grind)
    | exact superpose eq52712 eq14
    | exact resolve eq14 eq52712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53137 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq74
       have i₂ := eq53084
       grind)
    | exact superpose eq53084 eq74
    | exact resolve eq74 eq53084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq53084
  have eq53184 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq53137
       have i₂ := eq52712
       grind)
    | exact superpose eq52712 eq53137
    | exact resolve eq53137 eq52712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53263 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq53184
  have eq53269 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq53263
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq53263
    | exact resolve eq53263 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53263
  have eq53289 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq53269 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq53269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53269
  have eq53302 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq53289
  have eq53323 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by grind
  have eq54341 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq53085 X0
       have i₂ := eq52712
       grind)
    | exact superpose eq52712 eq53085
    | exact resolve eq53085 eq52712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53085
  have eq54648 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq54341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54341
  have eq54756 : ∀ X0 : G, (k (σ (M.op y y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq26457 y y X0
       have i₂ := eq54648 y
       grind)
    | exact superpose eq54648 eq26457
    | exact resolve eq26457 eq54648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26457
  have eq54759 : ∀ X0 : G, (k (M.op y y) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq26696 X0 y y
       have i₂ := eq54648 y
       grind)
    | exact superpose eq54648 eq26696
    | exact resolve eq26696 eq54648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26696 eq54648
  have eq55296 : ∀ X0 : G, (k y X0) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq54759 X0
       have i₂ := eq52712
       grind)
    | exact superpose eq52712 eq54759
    | exact resolve eq54759 eq52712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52712 eq54759
  have eq55334 : ∀ X0 : G, y = (M.op x x) ∨ (k y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq55296 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55296
  have eq55364 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (k y X0) = X0 := by
    intro X0
    grind
  clear eq55334
  have eq55467 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq55364 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55364
    | (have j0 := eq55364 X0
       grind)
    | exact resolve eq55364 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55364
  have eq55481 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq73
       have i₂ := eq55467 X0
       grind)
    | (have i₁ := eq73
       have i₂ := eq55467 x
       grind)
    | exact superpose eq55467 eq73
    | (have j1 := eq55467 X0
       grind)
    | exact resolve eq73 eq55467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55467
  have eq55512 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (k y X0) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq55481
    | (have j0 := eq55481 X0
       grind)
    | exact resolve eq55481 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55481
  have eq57500 : ∀ X0 : G, (k (k (σ y) (σ y)) X0) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq54756 X0
       have i₂ := eq53137
       grind)
    | exact superpose eq53137 eq54756
    | exact resolve eq54756 eq53137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53137 eq54756
  have eq57580 : ∀ X0 : G, (k (k (σ y) (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq57500 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57500
  have eq57865 : ∀ X0 : G, (k (M.op (σ y) (σ y)) X0) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq53323 eq57580
    | exact resolve eq57580 eq53323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53323 eq57580
  have eq57917 : ∀ X0 : G, (k (M.op (σ y) (σ y)) X0) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq57865 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57865
  have eq59072 : (σ y) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ y = (M.op x x) := by grind
  clear eq57917
  have eq59142 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq59072 eq14
    | exact resolve eq14 eq59072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59072
  have eq59603 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq53302 eq59142
    | exact resolve eq59142 eq53302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53302 eq59142
  have eq59912 : ∀ X0 : G, y = (M.op x x) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq59603 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59603
  have eq59971 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    grind
  clear eq59912
  have eq60074 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq59971 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq59971
    | (have j0 := eq59971 X0
       grind)
    | exact resolve eq59971 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59971
  have eq60088 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq73
       have i₂ := eq60074 X0
       grind)
    | (have i₁ := eq73
       have i₂ := eq60074 (k y x)
       grind)
    | exact superpose eq60074 eq73
    | (have j1 := eq60074 X0
       grind)
    | exact resolve eq73 eq60074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq60074
  have eq60118 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq60088
    | (have j0 := eq60088 X0
       grind)
    | exact resolve eq60088 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60088
  have eq60164 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 x
       have i₂ := eq60118 (k X0 x)
       grind)
    | exact superpose eq60118 eq11
    | (have j0 := eq11 (σ y) (σ y)
       have j1 := eq60118 (σ y)
       grind)
    | exact resolve eq11 eq60118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60118
  have eq60171 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq60164
    | (have j0 := eq60164 (σ y)
       grind)
    | exact resolve eq60164 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60164
  have eq60182 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq60171 (σ y)
       grind)
    | (have r₁ := eq60171 X0
       have r₂ := eq28
       grind)
    | exact resolve eq60171 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60171
  have eq535851 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j0 := eq60182 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60182
  have eq535852 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq535851
  have eq535987 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  have eq536070 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq535987 eq87
    | exact resolve eq87 eq535987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq535987
  have eq536174 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq535852 eq536070
    | exact resolve eq536070 eq535852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535852 eq536070
  have eq536427 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq536174
  have eq536440 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | exact superpose eq30 eq536427
    | exact resolve eq536427 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq536427
  have eq536449 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y y) := by grind
  clear eq536440
  have eq536552 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y y) := by
    first
    | exact superpose eq27 eq536449
    | exact resolve eq536449 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536449
  have eq536595 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k y X0) = X0 ∨ y = (k y y) := by
    intro X0
    first
    | exact superpose eq536552 eq55512
    | (have j0 := eq55512 X0
       grind)
    | exact resolve eq55512 eq536552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55512 eq536552
  have eq536645 : ∀ X0 : G, y = (k y y) ∨ (k y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq536595 y
       grind)
    | (have r₁ := eq536595 X0
       have r₂ := eq28
       grind)
    | exact resolve eq536595 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536595
  have eq536989 : y ≠ y ∨ y = (k y y) := by
    first
    | (have j0 := eq536645 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536645
  have eq536990 : y = (k y y) := by grind
  clear eq536989
  have eq537106 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq869 y
       have i₂ := eq536990
       grind)
    | exact superpose eq536990 eq869
    | (have j0 := eq869 y
       grind)
    | exact resolve eq869 eq536990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq537113 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq536990
       grind)
    | exact superpose eq536990 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq536990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536990
  have eq537128 : y = (M.op y y) := by grind
  clear eq537113
  have eq537133 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq537106
  have eq537148 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq537133
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq537133
    | exact resolve eq537133 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq537133
  have eq537305 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq54 y X0 y
       have i₂ := eq537128
       grind)
    | exact superpose eq537128 eq54
    | exact resolve eq54 eq537128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq537403 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq537305 X0
       have i₂ := eq537128
       grind)
    | exact superpose eq537128 eq537305
    | exact resolve eq537305 eq537128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537305
  have eq537481 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq537403 X0
       have i₂ := eq537128
       grind)
    | exact superpose eq537128 eq537403
    | exact resolve eq537403 eq537128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537128 eq537403
  have eq537647 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq537148 eq54
    | exact resolve eq54 eq537148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq537745 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq537148 eq537647
    | exact resolve eq537647 eq537148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537647
  have eq537823 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq537148 eq537745
    | exact resolve eq537745 eq537148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537148 eq537745
  have eq538875 : x = (M.op x y) := by
    first
    | (have i₁ := eq537481 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq537481
    | (have j0 := eq537481 x
       grind)
    | exact resolve eq537481 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq537481
  have eq539988 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq538875 eq21
    | exact resolve eq21 eq538875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq538875
  have eq540759 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq539988
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq539988
    | exact resolve eq539988 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq539988
  have eq542877 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq537823 eq27
    | (have j1 := eq537823 (σ x)
       grind)
    | exact resolve eq27 eq537823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq537823
  have eq543039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq540759 eq542877
    | exact resolve eq542877 eq540759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540759 eq542877
  have eq543404 : False := by grind
  exact eq543404

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq14 X0 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X1) ≠ (M.op (M.op X0 (M.op X1 X0)) X1) ∨ (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X0)) X1) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 (M.op X1 X0)) X1)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X1 (M.op X2 X1)) X2)
       have r₂ := eq14 (M.op (M.op X1 (M.op X2 X1)) X2) X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq64 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq66 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (M.op X1 X0)) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq14 X2 X0 X1
       grind)
    | exact superpose eq14 eq65
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
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
  have eq94 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq170 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq94 (σ X0) sF2
       grind)
    | exact superpose eq94 eq39
    | (have j1 := eq94 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq227 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (σ y)) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129 eq51
    | exact resolve eq51 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq235 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ y)))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq227 eq14
    | exact resolve eq14 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       have i₂ := eq53 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | (have r₁ := eq13 X0 (M.op X0 (M.op X2 (M.op X0 X2)))
       have r₂ := eq53 X0 (M.op X0 (M.op X2 (M.op X0 X2))) X2
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq460 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq473 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X0 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq468 X0 X1 X2
       have i₂ := eq53 X0 X2 X1
       grind)
    | exact superpose eq53 eq468
    | exact resolve eq468 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq519 : ∀ X0 : G, (k X0 (M.op (σ x) (M.op (σ y) (σ y)))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq227 eq66
    | exact resolve eq66 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq227
  have eq613 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq77
    | (have r₁ := eq77
       have r₂ := eq129
       grind)
    | exact resolve eq77 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq614 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq613
  have eq617 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq614 eq120
    | exact resolve eq120 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq621 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq617
  have eq626 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq621
       have r₂ := eq131
       grind)
    | exact resolve eq621 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq621
  have eq630 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq626 eq235
    | exact resolve eq235 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq638 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq626 eq519
    | exact resolve eq519 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq626
  have eq654 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq638 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq662 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq630 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq667 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq654
    | (have j0 := eq654 X0
       grind)
    | exact resolve eq654 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq672 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq662
    | (have j0 := eq662 X0
       grind)
    | exact resolve eq662 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq768 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129 eq667
    | exact resolve eq667 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq772 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq768 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq774 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129 eq672
    | exact resolve eq672 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq672
  have eq800 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq774 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq808 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq772 eq120
    | exact resolve eq120 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq772
  have eq813 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq808
  have eq1087 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq800
    | (have j0 := eq800 (σ x)
       grind)
    | exact resolve eq800 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq1157 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1087 eq27
    | exact resolve eq27 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq1167 : y = (M.op x y) := by
    first
    | (have r₁ := eq1157
       have r₂ := eq813
       grind)
    | exact resolve eq1157 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq1157
  have eq1168 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1167 eq20
    | exact resolve eq20 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : y ≠ y ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq1167 eq76
    | (have r₁ := eq76
       have r₂ := eq1167
       grind)
    | exact resolve eq76 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1176 : y = (k x y) ∨ y = (M.op y y) := by grind
  clear eq1172
  have eq1182 : (σ (M.op x y)) = (σ y) := by
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
  have eq1183 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1182 eq26
    | exact resolve eq26 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2068 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1176
       grind)
    | exact superpose eq1176 eq44
    | exact resolve eq44 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1176
  have eq2075 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1182 eq2068
    | exact resolve eq2068 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2077 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2075
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2075
    | exact resolve eq2075 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2075
  have eq2078 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1182 eq2077
    | exact resolve eq2077 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq2198 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2078 eq94
    | (have j0 := eq94 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq94 eq2078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq2078
  have eq2199 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y y) := by grind
  clear eq2198
  have eq2201 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1183 eq2199
    | exact resolve eq2199 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq2204 : y = (M.op y y) := by
    first
    | (have r₁ := eq2201
       have r₂ := eq27
       grind)
    | exact resolve eq2201 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq2221 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 y X0 y
       have i₂ := eq2204
       grind)
    | exact superpose eq2204 eq53
    | exact resolve eq53 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq2224 : ∀ X0 : G, (k X0 (M.op y (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq473 y y X0
       have i₂ := eq2204
       grind)
    | exact superpose eq2204 eq473
    | exact resolve eq473 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq2228 : ∀ X0 : G, (k X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2224 X0
       have i₂ := eq2204
       grind)
    | exact superpose eq2204 eq2224
    | exact resolve eq2224 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224
  have eq2231 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2221 X0
       have i₂ := eq2204
       grind)
    | exact superpose eq2204 eq2221
    | exact resolve eq2221 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq2239 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq2228 X0
       have i₂ := eq2204
       grind)
    | exact superpose eq2204 eq2228
    | exact resolve eq2228 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq2242 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq2231 X0
       have i₂ := eq2204
       grind)
    | exact superpose eq2204 eq2231
    | exact resolve eq2231 eq2204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204 eq2231
  have eq2406 : x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2242 x
       grind)
    | exact superpose eq2242 eq18
    | (have j1 := eq2242 x
       grind)
    | exact resolve eq18 eq2242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2242
  have eq2422 : x = y := by
    first
    | exact superpose eq1167 eq2406
    | exact resolve eq2406 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167 eq2406
  have eq2439 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2422
       grind)
    | exact superpose eq2422 eq24
    | exact resolve eq24 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2462 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq2239 X0
       have i₂ := eq2422
       grind)
    | exact superpose eq2422 eq2239
    | exact resolve eq2239 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239 eq2422
  have eq2473 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1182 eq2439
    | exact resolve eq2439 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182 eq2439
  have eq2482 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2473
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2473
    | exact resolve eq2473 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2473
  have eq2515 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2482 eq1183
    | exact resolve eq1183 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq4688 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq2482 eq170
    | (have j0 := eq170 X0
       grind)
    | exact resolve eq170 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq4689 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4688 X0
       have i₂ := eq2462 X0
       grind)
    | exact superpose eq2462 eq4688
    | (have j0 := eq4688 X0
       grind)
    | exact resolve eq4688 eq2462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462 eq4688
  have eq4690 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2482 eq4689
    | (have j0 := eq4689 X0
       grind)
    | exact resolve eq4689 eq2482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482 eq4689
  have eq4709 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq4690
    | (have j0 := eq4690 (M.op x y)
       grind)
    | exact resolve eq4690 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4690
  have eq4719 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq4709
  have eq4722 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2515 eq4719
    | exact resolve eq4719 eq2515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515 eq4719
  have eq4735 : False := by grind
  exact eq4735

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_x_pxy_Equation1061 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq14 X0 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
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
  have eq70 : y ≠ (M.op x y) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq120
  have eq124 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq123
  have eq163 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq124 eq16
    | exact resolve eq16 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq212 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq378 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq833
    | exact resolve eq833 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq837 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq834
       have r₂ := eq28
       grind)
    | exact resolve eq834 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq839 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq837
    | exact resolve eq837 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837
  have eq841 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq839 eq71
    | (have r₁ := eq71
       have r₂ := eq839
       grind)
    | exact resolve eq71 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq839
  have eq845 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq841
  have eq846 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq845
  have eq887 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (M.op (σ X1) (σ (k X0 X1))))) = X2 ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (σ X0) X2 (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq56
    | (have j1 := eq76 X0 X1
       grind)
    | exact resolve eq56 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq914 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq846 eq88
    | exact resolve eq88 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq915 : (τ (σ x)) = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq846 eq61
    | exact resolve eq61 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq846
  have eq918 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq914
  have eq922 : x = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq915
    | exact resolve eq915 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq925 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq922
       have r₂ := eq70
       grind)
    | exact resolve eq922 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq922
  have eq952 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq918 eq30
    | exact resolve eq30 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq918
  have eq972 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq952
    | exact resolve eq952 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq973 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq972
  have eq977 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq973 eq29
    | exact resolve eq29 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1000 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq977
    | exact resolve eq977 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1057 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1000 eq21
    | exact resolve eq21 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1066 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1000 eq212
    | exact resolve eq212 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1081 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1057
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1057
    | exact resolve eq1057 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq3345 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq378 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq56 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
       grind)
    | exact superpose eq56 eq378
    | exact resolve eq378 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq3483 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1))))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3345 X0 X1 X2
       have i₂ := eq45 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq45 eq3345
    | exact resolve eq3345 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345
  have eq3507 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3483 X0 X1 X2
       have i₂ := eq56 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
       grind)
    | exact superpose eq56 eq3483
    | exact resolve eq3483 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3483
  have eq3524 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3507 X0 X1 X2
       have i₂ := eq45 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq45 eq3507
    | exact resolve eq3507 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3507
  have eq3541 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3524 X0 X1 X2
       have i₂ := eq56 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
       grind)
    | exact superpose eq56 eq3524
    | exact resolve eq3524 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3524
  have eq29630 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq887 x y X0
       have i₂ := eq925
       grind)
    | exact superpose eq925 eq887
    | (have j0 := eq887 x y x
       grind)
    | exact resolve eq887 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq925
  have eq30042 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq29630 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29630
    | (have j0 := eq29630 X0
       grind)
    | exact resolve eq29630 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29630
  have eq30150 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30042 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30042
    | (have j0 := eq30042 X0
       grind)
    | exact resolve eq30042 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30042
  have eq30256 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30150 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30150
    | (have j0 := eq30150 X0
       grind)
    | exact resolve eq30150 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30150
  have eq30316 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30256 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30256
    | (have j0 := eq30256 X0
       grind)
    | exact resolve eq30256 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30256
  have eq30370 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq30316
    | (have j0 := eq30316 X0
       grind)
    | exact resolve eq30316 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30316
  have eq30418 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30370 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq30370
    | (have j0 := eq30370 X0
       grind)
    | exact resolve eq30370 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30370
  have eq30444 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30418 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30418
    | (have j0 := eq30418 X0
       grind)
    | exact resolve eq30418 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30418
  have eq30445 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30444 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30444
  have eq880240 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f880240_15 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
      intro X0 X1 X2
      grind
    have f880240_16 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0
      grind
    have f880240_25 : X0 ≠ (M.op X0 (σ y)) := by grind
    have f880240_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f880240_27 : (σ x) ≠ (σ y) := by grind
    have f880240_28 : x ≠ y := by grind
    have f880240_30 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0
      first
      | (have j0 := f880240_16 X0
         grind)
      | (have r₁ := f880240_16 X0
         have r₂ := f880240_26
         grind)
      | exact resolve f880240_16 f880240_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f880240_31 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = y := by
      intro X0
      first
      | (have j0 := f880240_30 X0
         grind)
      | (have r₁ := f880240_30 X0
         have r₂ := f880240_27
         grind)
      | exact resolve f880240_30 f880240_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f880240_32 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f880240_31 X0
         grind)
      | (have r₁ := f880240_31 X0
         have r₂ := f880240_28
         grind)
      | exact resolve f880240_31 f880240_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f880240_67 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f880240_15 (σ y) X0 (σ x)
         have i₂ := f880240_32 (σ y)
         grind)
      | exact superpose f880240_32 f880240_15
      | exact resolve f880240_15 f880240_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f880240_73 : X0 ≠ X0 := by
      first
      | (have i₁ := f880240_25
         have i₂ := f880240_67 X0
         grind)
      | exact superpose f880240_67 f880240_25
      | (have r₁ := f880240_25
         have r₂ := f880240_67 X0
         grind)
      | exact resolve f880240_25 f880240_67
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f880240_79 : False := by grind
    exact f880240_79
  clear eq56 eq30445
  have eq881281 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1081 eq880240
    | exact resolve eq880240 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq880240
  have eq882077 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq881281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881281
  have eq882315 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq882077 X0
       grind)
    | (have r₁ := eq882077 X0
       have r₂ := eq28
       grind)
    | exact resolve eq882077 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882077
  have eq883255 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq882315 eq163
    | exact resolve eq163 eq882315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq882315
  have eq883300 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq883255
    | exact resolve eq883255 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883255
  have eq883536 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1000 eq883300
    | exact resolve eq883300 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883300
  have eq883735 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq883536
  have eq884038 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1066 X0
       have i₂ := eq883735
       grind)
    | exact superpose eq883735 eq1066
    | exact resolve eq1066 eq883735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq883735
  have eq884157 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq884038 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884038
  have eq884196 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq884157 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq884157
    | (have j0 := eq884157 X0
       grind)
    | exact resolve eq884157 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884157
  have eq884400 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1000 eq884196
    | exact resolve eq884196 eq1000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq884196
  have eq885301 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq884400 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884400
  have eq886562 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq885301 x
       grind)
    | exact superpose eq885301 eq19
    | (have j1 := eq885301 x
       grind)
    | exact resolve eq19 eq885301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885301
  have eq886611 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq886562
  have eq886930 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq886611 eq29
    | exact resolve eq29 eq886611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq886611
  have eq888223 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq886930
    | exact resolve eq886930 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq886930
  have eq888224 : x = (M.op x y) ∨ x = y := by grind
  clear eq888223
  have eq888232 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq888224 eq21
    | exact resolve eq21 eq888224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888281 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq888224 eq212
    | exact resolve eq212 eq888224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq888224
  have eq889143 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq888232
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq888232
    | exact resolve eq888232 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888232
  have eq889174 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq889143 eq27
    | exact resolve eq27 eq889143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889143
  have eq904133 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3541 y x X0
       have i₂ := eq888281 y
       grind)
    | exact superpose eq888281 eq3541
    | exact resolve eq3541 eq888281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3541 eq888281
  have eq905160 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq904133 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq904133
    | (have j0 := eq904133 X0
       grind)
    | exact resolve eq904133 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904133
  have eq906969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq905160 eq889174
    | exact resolve eq889174 eq905160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889174 eq905160
  have eq907034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq906969
  have eq907050 : x = y := by
    first
    | (have r₁ := eq907034
       have r₂ := eq28
       grind)
    | exact resolve eq907034 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907034
  have eq907286 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq907050
       grind)
    | exact superpose eq907050 eq19
    | exact resolve eq19 eq907050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq907287 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq907050
       grind)
    | exact superpose eq907050 eq25
    | exact resolve eq25 eq907050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq907050
  have eq907626 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq907287
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq907287
    | exact resolve eq907287 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq907287
  have eq907656 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq907626 eq27
    | exact resolve eq27 eq907626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq907626
  have eq908651 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq907656 eq69
    | exact resolve eq69 eq907656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq907656
  have eq908767 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq908651
       have i₂ := eq907286
       grind)
    | exact superpose eq907286 eq908651
    | exact resolve eq908651 eq907286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907286 eq908651
  have eq908793 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq908767 eq15
    | exact resolve eq15 eq908767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908767
  have eq909126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq908793
    | exact resolve eq908793 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq908793
  have eq909228 : False := by grind
  exact eq909228

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_pyy_pxy_pyy_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq52 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq52 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq52 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq160 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq165 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq160 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | (have r₁ := eq160 X0 X0
       have r₂ := eq54 X0 X0
       grind)
    | exact resolve eq160 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq160
  have eq355 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq165 (σ X0) (σ X1)
       grind)
    | exact superpose eq165 eq15
    | exact resolve eq15 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 X1
       have i₂ := eq165 X0 X1
       grind)
    | exact superpose eq165 eq355
    | exact resolve eq355 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq355
  have eq365 : False := by grind
  exact eq365

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq75 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq41
    | exact resolve eq41 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq41 X1
       grind)
    | exact superpose eq41 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq83
  have eq146 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq89
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq89 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq89
    | exact resolve eq89 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq170 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 X0 X1 X2
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq151
    | (have j0 := eq151 X0 X1 X2
       grind)
    | exact resolve eq151 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq151
  have eq173 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq146 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq146
    | (have j0 := eq146 X0 X1
       grind)
    | exact resolve eq146 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq146
  have eq179 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq173 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq173 (σ X0) (M.op X0 X0)
       have r₂ := eq77 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq173 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq173
  have eq577 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq179
    | exact resolve eq179 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2098 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X2) (k X0 (σ X1))
       have i₂ := eq170 X0 X1 X2
       grind)
    | exact superpose eq170 eq13
    | (have j0 := eq13 (σ X2) (k X0 (σ X1))
       have j1 := eq170 X0 X1 X2
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq170 X0 X1 X2
       grind)
    | exact resolve eq13 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq2100 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2098 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq2101 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (k (σ X2) (k X0 (σ X1))) ∨ (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2100 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq2103 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (k X2 (k (τ X0) X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2101 X0 X1 X2
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq2101
    | (have j0 := eq2101 X0 X1 X2
       grind)
    | exact resolve eq2101 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2101
  have eq56953 : ∀ X0 X1 X2 : G, (M.op (k X1 X0) (k X1 X0)) = (M.op (k X1 X0) (σ X2)) ∨ (k X1 X0) = (σ (k X2 (k (τ X1) (τ X0)))) ∨ (M.op (σ X2) (k X1 X0)) = (σ (k X2 (k (τ X1) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2103 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2103
    | exact resolve eq2103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103
  have eq57318 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (k X2 (τ (k X1 X0)))) ∨ (M.op (k X1 X0) (k X1 X0)) = (M.op (k X1 X0) (σ X2)) ∨ (M.op (σ X2) (k X1 X0)) = (σ (k X2 (k (τ X1) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56953 X0 X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq56953
    | (have j0 := eq56953 X0 X1 X2
       grind)
    | exact resolve eq56953 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56953
  have eq57374 : ∀ X0 X1 X2 : G, (k X1 X0) = (k (σ X2) (k X1 X0)) ∨ (M.op (k X1 X0) (k X1 X0)) = (M.op (k X1 X0) (σ X2)) ∨ (M.op (σ X2) (k X1 X0)) = (σ (k X2 (k (τ X1) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57318 X0 X1 X2
       have i₂ := eq18 (k X1 X0) X2
       grind)
    | exact superpose eq18 eq57318
    | (have j0 := eq57318 X0 X1 X2
       grind)
    | exact resolve eq57318 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57318
  have eq57420 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X1 X0)) = (σ (k X2 (τ (k X1 X0)))) ∨ (k X1 X0) = (k (σ X2) (k X1 X0)) ∨ (M.op (k X1 X0) (k X1 X0)) = (M.op (k X1 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57374 X0 X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq57374
    | (have j0 := eq57374 X0 X1 X2
       grind)
    | exact resolve eq57374 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq57374
  have eq57433 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X1 X0)) = (k (σ X2) (k X1 X0)) ∨ (k X1 X0) = (k (σ X2) (k X1 X0)) ∨ (M.op (k X1 X0) (k X1 X0)) = (M.op (k X1 X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57420 X0 X1 X2
       have i₂ := eq18 (k X1 X0) X2
       grind)
    | exact superpose eq18 eq57420
    | (have j0 := eq57420 X0 X1 X2
       grind)
    | exact resolve eq57420 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq57420
  have eq57444 : ∀ X0 X1 X2 : G, (k X1 X0) = (k (σ X2) (k X1 X0)) ∨ (M.op (σ X2) (k X1 X0)) = (k (σ X2) (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq57433 X0 X1 X2
       have j1 := eq12 (σ X2) (k X1 X0)
       grind)
    | (have r₁ := eq57433 X0 X1 X2
       have r₂ := eq12 (σ X2) (k X1 X0)
       grind)
    | exact resolve eq57433 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57433
  have eq76782 : ∀ X0 X1 X2 : G, (k X1 X2) ≠ (M.op (σ X0) (k X1 X2)) ∨ (k (σ X0) (k X1 X2)) = (M.op (σ X0) (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq57444 X2 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57444
  have eq76796 : ∀ X0 X1 X2 : G, (k (σ X0) (k X1 X2)) = (M.op (σ X0) (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq76782 X0 X1 X2
       have j1 := eq577 (k X1 X2) (σ X0)
       grind)
    | (have r₁ := eq76782 X0 X1 X2
       have r₂ := eq577 (k X1 X2) (σ X0)
       grind)
    | exact resolve eq76782 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76782
  have eq77210 : ∀ X0 X1 X2 : G, (k X0 (k X1 X2)) = (M.op X0 (k X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq76796 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq76796
    | exact resolve eq76796 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76796
  have eq77541 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77210 X0 X0 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq77210
    | exact resolve eq77210 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq77542 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X1)) = (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77210 X0 X1 X0
       have i₂ := eq577 X0 X1
       grind)
    | exact superpose eq577 eq77210
    | (have j1 := eq577 (M.op X0 X1) X2
       grind)
    | exact resolve eq77210 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq77210
  have eq159050 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X3)) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq77542 X0 (M.op (M.op X1 (M.op X2 X2)) X0) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq77542
    | (have j0 := eq77542 (M.op X2 (M.op X3 X3)) X0 X2
       grind)
    | exact resolve eq77542 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77542
  have eq168983 : ∀ X0 X3 : G, (M.op X0 X0) = X0 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X3
    first
    | (have i₁ := eq9 X0 x x
       have i₂ := eq159050 X0 X3 x x
       grind)
    | exact superpose eq159050 eq9
    | (have j1 := eq159050 X0 X3 x X3
       grind)
    | exact resolve eq9 eq159050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159050
  have eq170530 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77541 X0 X1
       have i₂ := eq168983 X0 x
       grind)
    | exact superpose eq168983 eq77541
    | (have j1 := eq168983 X0 X1
       grind)
    | exact resolve eq77541 eq168983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77541 eq168983
  have eq171225 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq170530 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170530
  have eq171226 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq171225 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171225
  have eq175144 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq171226 (σ X0) (σ X1)
       grind)
    | exact superpose eq171226 eq15
    | exact resolve eq15 eq171226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175437 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq175144 X0 X1
       have i₂ := eq171226 X0 X1
       grind)
    | exact superpose eq171226 eq175144
    | exact resolve eq175144 eq171226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171226 eq175144
  have eq191299 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175437 x y
       grind)
    | exact superpose eq175437 eq16
    | (have r₁ := eq16
       have r₂ := eq175437 x y
       grind)
    | exact resolve eq16 eq175437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175437
  have eq191514 : False := by grind
  exact eq191514

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq42
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq49 X0 X1
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq49 X0 X1
       grind)
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq50
  have eq95 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq47 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq99 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq95 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq95 X0 X0
       have r₂ := eq52 X0 X0
       grind)
    | exact resolve eq95 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq95
  have eq213 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq99 (σ X0) (σ X1)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq213 X0 X1
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq213
    | exact resolve eq213 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq213
  have eq222 : False := by grind
  exact eq222

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) X0) ≠ X0 ∨ (k (M.op (M.op X1 (M.op X2 X2)) X0) X0) = (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 (M.op X2 X2)) X0) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op X1 (M.op X2 X2))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1
    grind
  have eq95 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
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
  have eq2325 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq66
  have eq2356 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2325 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325
  have eq4474 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) ∨ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    grind
  clear eq64
  have eq4475 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4474 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4474
  have eq4476 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4475 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4475
  have eq18841 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq12
    | (have j0 := eq12 (τ X0) X1
       have j1 := eq95 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq95 X0 (M.op X1 (τ X0))
       grind)
    | exact resolve eq12 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq18860 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq18841 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18841
  have eq30980 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4476 x x
       have i₂ := eq2356 x x
       grind)
    | exact superpose eq2356 eq4476
    | (have j1 := eq2356 X0 x
       grind)
    | exact resolve eq4476 eq2356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2356 eq4476
  have eq31057 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq30980 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30980
  have eq31172 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31057 (σ X0)
       grind)
    | exact superpose eq31057 eq15
    | exact resolve eq15 eq31057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31233 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31172 X0
       have i₂ := eq31057 X0
       grind)
    | exact superpose eq31057 eq31172
    | exact resolve eq31172 eq31057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31057 eq31172
  have eq199431 : ∀ X0 X1 : G, (τ (k X0 (σ X1))) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq18860 X0 X1
       grind)
    | exact superpose eq18860 eq10
    | (have j1 := eq18860 X0 X1
       grind)
    | exact resolve eq10 eq18860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18860
  have eq199573 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq199431 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq199431
    | (have j0 := eq199431 X0 X1
       grind)
    | exact resolve eq199431 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq199431
  have eq199574 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq199573 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199573
  have eq199883 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199574 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq199574
    | exact resolve eq199574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199974 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq199574 X0 X1
       grind)
    | exact superpose eq199574 eq18
    | (have j1 := eq199574 X0 X1
       grind)
    | exact resolve eq18 eq199574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq199574
  have eq200388 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq199883 (σ X0) (σ X1)
       grind)
    | exact superpose eq199883 eq15
    | (have j1 := eq199883 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq199883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199883
  have eq200897 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199974 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq199974
    | exact resolve eq199974 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199974
  have eq201329 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq200897 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq200897
    | (have j0 := eq200897 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq200897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200897
  have eq206125 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200388 x y
       grind)
    | exact superpose eq200388 eq16
    | (have j1 := eq200388 x y
       grind)
    | exact resolve eq16 eq200388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200388
  have eq206611 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq206125
       have i₂ := eq201329 x y
       grind)
    | exact superpose eq201329 eq206125
    | (have j1 := eq201329 (σ x) (σ y)
       grind)
    | (have r₁ := eq206125
       have r₂ := eq201329 x y
       grind)
    | (have r₁ := eq206125
       have r₂ := eq201329 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq206125
       have r₂ := eq201329 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq206125 eq201329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201329 eq206125
  have eq206614 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq206611
  have eq206617 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206614
       grind)
    | exact superpose eq206614 eq16
    | exact resolve eq16 eq206614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206614
  have eq206618 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq206617
       have r₂ := eq31233 x
       grind)
    | exact resolve eq206617 eq31233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206617
  have eq206619 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206618
       grind)
    | exact superpose eq206618 eq16
    | exact resolve eq16 eq206618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206620 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq206618
       grind)
    | exact superpose eq206618 eq10
    | exact resolve eq10 eq206618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206618
  have eq206783 : x = y := by
    first
    | (have i₁ := eq206620
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq206620
    | exact resolve eq206620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206620
  have eq206784 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq206619
       have i₂ := eq31233 x
       grind)
    | exact superpose eq31233 eq206619
    | exact resolve eq206619 eq31233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31233 eq206619
  have eq206823 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq206784
       have i₂ := eq206783
       grind)
    | exact superpose eq206783 eq206784
    | exact resolve eq206784 eq206783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206783 eq206784
  have eq206824 : False := by grind
  exact eq206824

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyy_pxy_pyy_pxy_Equation1242 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
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
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq48 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq50 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq50 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq51 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq51
    | (have j0 := eq51 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq51 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq51 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq109 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq99 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq109 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq109 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq109 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq114 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq20 X1
       grind)
    | exact superpose eq20 eq113
    | (have j0 := eq113 X0 X1
       grind)
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq113
  have eq137 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq141 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq137 X0 X1
       have j1 := eq114 X0 X1
       grind)
    | (have r₁ := eq137 X0 X1
       have r₂ := eq114 X0 X1
       grind)
    | (have r₁ := eq137 X1 X1
       have r₂ := eq114 X1 X1
       grind)
    | exact resolve eq137 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq137
  have eq428 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq141 (σ X0) (σ X1)
       grind)
    | exact superpose eq141 eq15
    | exact resolve eq15 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq428 X0 X1
       have i₂ := eq141 X0 X1
       grind)
    | exact superpose eq141 eq428
    | exact resolve eq428 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq428
  have eq438 : False := by grind
  exact eq438
