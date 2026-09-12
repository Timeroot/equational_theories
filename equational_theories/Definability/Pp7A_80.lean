import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_pxx_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x y) X0) y) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq220 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X0) (M.op X1 X0)) = X1 ∨ (M.op X1 X1) = (k X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (M.op X1 X0)
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq54 X1 X1
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq464 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq73 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq11037 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11037
    | exact resolve eq11037 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11037
  have eq11049 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11038
       have r₂ := eq28
       grind)
    | exact resolve eq11038 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11038
  have eq11051 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11049
    | exact resolve eq11049 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11049
  have eq11168 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11051
  have eq11183 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11168
    | exact resolve eq11168 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11168
  have eq11338 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11183 eq95
    | exact resolve eq95 eq11183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11183
  have eq11351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11338
  have eq11353 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11351
       have r₂ := eq28
       grind)
    | exact resolve eq11351 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11351
  have eq11409 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11353
  have eq11424 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11409
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11409
    | exact resolve eq11409 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11409
  have eq11578 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11424
       grind)
    | exact superpose eq11424 eq70
    | exact resolve eq70 eq11424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11424
  have eq11602 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11578
    | exact resolve eq11578 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11578
  have eq11788 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11602 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11788
    | exact resolve eq11788 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11788
  have eq11802 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11791
       have r₂ := eq28
       grind)
    | exact resolve eq11791 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11791
  have eq11804 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11802
    | exact resolve eq11802 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11802
  have eq11805 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11804
  have eq11922 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11805
  have eq11937 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11922
    | exact resolve eq11922 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11922
  have eq12099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11937 eq11602
    | exact resolve eq11602 eq11937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11602 eq11937
  have eq12106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12099
  have eq12110 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12106
       have r₂ := eq28
       grind)
    | exact resolve eq12106 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12106
  have eq12226 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12110 eq28
    | exact resolve eq28 eq12110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12227 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12110 eq52
    | exact resolve eq52 eq12110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq12516 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12227
    | (have j0 := eq12227 (σ y)
       grind)
    | exact resolve eq12227 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12227
  have eq12657 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12110 eq12516
    | exact resolve eq12516 eq12110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12516
  have eq12673 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12657
  have eq12676 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq12673
    | exact resolve eq12673 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12673
  have eq12688 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12676 eq220
    | exact resolve eq220 eq12676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12676
  have eq12689 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq12688
  have eq13076 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12110 eq12689
    | exact resolve eq12689 eq12110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12689
  have eq13088 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13076
  have eq13093 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13088
  have eq13112 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq13093
    | exact resolve eq13093 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13093
  have eq13147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq95 eq13112
    | exact resolve eq13112 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq13166 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq13112
  have eq13170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq13147
  have eq13172 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13166
       have r₂ := eq12110
       grind)
    | exact resolve eq13166 eq12110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12110 eq13166
  have eq13174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq13170
       have r₂ := eq12226
       grind)
    | exact resolve eq13170 eq12226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12226 eq13170
  have eq13175 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13174
       have r₂ := eq28
       grind)
    | exact resolve eq13174 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13174
  have eq13184 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13172 eq92
    | exact resolve eq92 eq13172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq13172
  have eq13222 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq13184
    | exact resolve eq13184 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq13184
  have eq13229 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq13175
  have eq13244 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13229
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13229
    | exact resolve eq13229 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13229
  have eq13343 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13222
       have i₂ := eq13244
       grind)
    | exact superpose eq13244 eq13222
    | exact resolve eq13222 eq13244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13222 eq13244
  have eq13350 : x = (M.op x y) := by grind
  clear eq13343
  have eq13383 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13350 eq21
    | exact resolve eq21 eq13350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq13385 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op x X0) y) := by
    intro X0
    first
    | exact superpose eq13350 eq51
    | exact resolve eq51 eq13350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq13494 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13383
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13383
    | exact resolve eq13383 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13383
  have eq13496 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13494 eq27
    | exact resolve eq27 eq13494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13970 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq13385 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13385
    | (have j0 := eq13385 y
       grind)
    | exact resolve eq13385 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13385
  have eq13994 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq13350 eq13970
    | exact resolve eq13970 eq13350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13970
  have eq13996 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq13994
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13994
    | exact resolve eq13994 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13994
  have eq13998 : x = (M.op y y) := by
    first
    | exact superpose eq13350 eq13996
    | exact resolve eq13996 eq13350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13996
  have eq14015 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq220 y y
       have i₂ := eq13998
       grind)
    | exact superpose eq13998 eq220
    | exact resolve eq220 eq13998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq13998
  have eq14016 : y = (M.op x x) ∨ x = (k y x) := by grind
  clear eq14015
  have eq15112 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq14016
  have eq15128 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq15112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15112
    | exact resolve eq15112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15112
  have eq15134 : x = (k y x) ∨ x = (k y x) := by
    first
    | exact superpose eq13350 eq15128
    | exact resolve eq15128 eq13350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13350 eq15128
  have eq15135 : x = (k y x) := by grind
  clear eq15134
  have eq15141 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq15135
       grind)
    | exact superpose eq15135 eq70
    | exact resolve eq70 eq15135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq15155 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq464 x y
       have i₂ := eq15135
       grind)
    | exact superpose eq15135 eq464
    | (have j0 := eq464 x y
       grind)
    | exact resolve eq464 eq15135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464 eq15135
  have eq15158 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq15155
  have eq15166 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15158
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15158
    | exact resolve eq15158 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15158
  have eq15178 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq13494 eq15141
    | exact resolve eq15141 eq13494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15141
  have eq15180 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15166
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15166
    | exact resolve eq15166 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15166
  have eq15192 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq15178
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15178
    | exact resolve eq15178 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15178
  have eq15193 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq15180
    | exact resolve eq15180 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15180
  have eq15203 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq13494 eq15192
    | exact resolve eq15192 eq13494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15192
  have eq15204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13494 eq15193
    | exact resolve eq15193 eq13494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15193
  have eq15209 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq15204
       have r₂ := eq28
       grind)
    | exact resolve eq15204 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15204
  have eq15214 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15209
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15209
    | exact resolve eq15209 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15209
  have eq15219 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq13494 eq15214
    | exact resolve eq15214 eq13494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13494 eq15214
  have eq15223 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq15219
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15219
    | exact resolve eq15219 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15219
  have eq15293 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq15223
  have eq15308 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq13496 eq15293
    | exact resolve eq15293 eq13496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13496 eq15293
  have eq15309 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15203 eq15308
    | exact resolve eq15308 eq15203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15203 eq15308
  have eq15310 : False := by grind
  exact eq15310

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pxx_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X1 X0) X1
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq322 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq326 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq322 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq327 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq325 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq325 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq325 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq340 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq327 (σ X0)
       grind)
    | exact superpose eq327 eq15
    | exact resolve eq15 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq340 X0
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq340
    | exact resolve eq340 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq340
  have eq406 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq64
    | exact resolve eq64 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq406 X0
       have i₂ := eq359 (M.op X0 X0)
       grind)
    | exact superpose eq359 eq406
    | exact resolve eq406 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq416 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq412 X0
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq412
    | exact resolve eq412 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq412
  have eq749 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq326 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq750 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq749 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq762 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq750 X1 (τ X0)
       grind)
    | exact superpose eq750 eq18
    | (have j1 := eq750 X1 (τ X0)
       grind)
    | exact resolve eq18 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq765 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq750 (σ X1) (σ X0)
       grind)
    | exact superpose eq750 eq15
    | (have j1 := eq750 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq1061 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq762 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq762
    | exact resolve eq762 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq1122 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1061 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1061
    | (have j0 := eq1061 X0 X1
       grind)
    | exact resolve eq1061 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061
  have eq2400 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq765 x y
       grind)
    | exact superpose eq765 eq16
    | (have j1 := eq765 x y
       grind)
    | exact resolve eq16 eq765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq2531 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2400
       have i₂ := eq1122 x y
       grind)
    | exact superpose eq1122 eq2400
    | (have j1 := eq1122 (σ x) (σ y)
       grind)
    | (have r₁ := eq2400
       have r₂ := eq1122 x y
       grind)
    | exact resolve eq2400 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122 eq2400
  have eq2532 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq2531
  have eq2535 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op y X0) x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq2532
       grind)
    | exact superpose eq2532 eq9
    | exact resolve eq9 eq2532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2582 : (M.op y x) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2535 x
       have i₂ := eq2532
       grind)
    | exact superpose eq2532 eq2535
    | exact resolve eq2535 eq2532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535
  have eq2598 : (M.op y x) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq2582
  have eq2600 : y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2532
       have i₂ := eq2598
       grind)
    | exact superpose eq2598 eq2532
    | exact resolve eq2532 eq2598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532 eq2598
  have eq2616 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2600
  have eq2695 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (σ y) X0) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ x) (σ y)
       have i₂ := eq2616
       grind)
    | exact superpose eq2616 eq9
    | exact resolve eq9 eq2616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2816 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2695 (σ x)
       have i₂ := eq2616
       grind)
    | exact superpose eq2616 eq2695
    | exact resolve eq2695 eq2616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2695
  have eq2836 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2816
  have eq2839 : (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2836
       have i₂ := eq359 x
       grind)
    | exact superpose eq359 eq2836
    | exact resolve eq2836 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq2836
  have eq2843 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2616
       have i₂ := eq2839
       grind)
    | exact superpose eq2839 eq2616
    | exact resolve eq2616 eq2839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2616 eq2839
  have eq2864 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq2843
  have eq2884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq416 x
       have i₂ := eq2864
       grind)
    | exact superpose eq2864 eq416
    | exact resolve eq416 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864
  have eq2915 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq2884
       have r₂ := eq16
       grind)
    | exact resolve eq2884 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884
  have eq2924 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2915
       grind)
    | exact superpose eq2915 eq10
    | exact resolve eq10 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915
  have eq2982 : y = (M.op x x) := by
    first
    | (have i₁ := eq2924
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2924
    | exact resolve eq2924 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2924
  have eq3012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq416 x
       have i₂ := eq2982
       grind)
    | exact superpose eq2982 eq416
    | exact resolve eq416 eq2982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq2982
  have eq3043 : False := by grind
  exact eq3043

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq22
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24 eq36
  have eq72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq72 y x
       grind)
    | exact superpose eq72 eq69
    | (have j1 := eq72 y x
       grind)
    | exact resolve eq69 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq111 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq112 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq112 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq43
    | exact resolve eq43 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq117 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq70
    | exact resolve eq70 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq118 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq49
    | exact resolve eq49 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq119 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq82
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq82
    | exact resolve eq82 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq120 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq119
       have i₂ := eq113 y
       grind)
    | exact superpose eq113 eq119
    | exact resolve eq119 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq121 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq118
    | exact resolve eq118 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq122 : (σ (M.op y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq113 sF3
       grind)
    | exact superpose eq113 eq117
    | exact resolve eq117 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq123 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq116
    | exact resolve eq116 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq116
  have eq252 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq102 eq72
    | (have j0 := eq72 (σ y) (σ x)
       grind)
    | exact resolve eq72 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq855
    | exact resolve eq855 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq859 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq856
       have r₂ := eq27
       grind)
    | exact resolve eq856 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq861 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq859
    | exact resolve eq859 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq907 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq861 eq111
    | (have r₁ := eq111
       have r₂ := eq861
       grind)
    | exact resolve eq111 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq908 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq861 eq121
    | exact resolve eq121 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq911 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq861 eq53
    | exact resolve eq53 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq917 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq907
  have eq919 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq253 eq911
    | exact resolve eq911 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq923 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq919 eq53
    | exact resolve eq53 eq919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq925 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq923
    | exact resolve eq923 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq940 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq925 eq51
    | exact resolve eq51 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq954 : (M.op x y) ≠ (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq908
  have eq1105 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq940 eq925
    | exact resolve eq925 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq940
  have eq1113 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1105
  have eq1115 : (M.op y y) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1113 eq120
    | exact resolve eq120 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq1183 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq1115
       grind)
    | exact superpose eq1115 eq53
    | exact resolve eq53 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1751 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq917 eq102
    | exact resolve eq102 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq917
  have eq1754 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1751
  have eq1762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1754 eq1113
    | exact resolve eq1113 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113 eq1754
  have eq1773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1762
  have eq1779 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1773
       have r₂ := eq27
       grind)
    | exact resolve eq1773 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773
  have eq1783 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq1779
       grind)
    | exact superpose eq1779 eq123
    | exact resolve eq123 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1788 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq1779
       grind)
    | exact superpose eq1779 eq53
    | exact resolve eq53 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1794 : (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq252 eq1788
    | exact resolve eq1788 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788
  have eq1795 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1783
    | exact resolve eq1783 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783
  have eq1856 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq1794
       grind)
    | exact superpose eq1794 eq53
    | exact resolve eq53 eq1794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq1858 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1856
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1856
    | exact resolve eq1856 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq1871 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1795 eq53
    | exact resolve eq53 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1873 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (σ (M.op x y)) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1795 eq14
    | exact resolve eq14 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1987 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1858 eq50
    | exact resolve eq50 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2368 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1987 eq1858
    | exact resolve eq1858 eq1987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858 eq1987
  have eq2376 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2368
  have eq2380 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq2376
       grind)
    | exact superpose eq2376 eq122
    | exact resolve eq122 eq2376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2376
  have eq2391 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2380
    | exact resolve eq2380 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2380
  have eq2461 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2391 eq53
    | exact resolve eq53 eq2391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2391
  have eq2676 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2461 eq1873
    | exact resolve eq1873 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq2683 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2676
  have eq2712 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2683 eq53
    | exact resolve eq53 eq2683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2714 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2712
    | exact resolve eq2712 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2712
  have eq2717 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1871 eq2714
    | exact resolve eq2714 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871 eq2714
  have eq2724 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2717
  have eq2726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2724 eq2461
    | exact resolve eq2461 eq2724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461 eq2724
  have eq2735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2726
  have eq2737 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2735
       have r₂ := eq27
       grind)
    | exact resolve eq2735 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq2904 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq2737 eq27
    | exact resolve eq27 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq2906 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2737 eq253
    | exact resolve eq253 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq2916 : (M.op x y) ≠ (τ (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2737 eq954
    | exact resolve eq954 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq2922 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2737 eq1183
    | exact resolve eq1183 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq2927 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq2922
    | exact resolve eq2922 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2922
  have eq2929 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq28 eq2916
    | exact resolve eq2916 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2916
  have eq2933 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2927
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2927
    | exact resolve eq2927 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2927
  have eq2941 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq2906 eq53
    | exact resolve eq53 eq2906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2906
  have eq2948 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq2941
    | exact resolve eq2941 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2941
  have eq2952 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq2737 eq2948
    | exact resolve eq2948 eq2737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2737 eq2948
  have eq2972 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2933
       have r₂ := eq2929
       grind)
    | exact resolve eq2933 eq2929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929 eq2933
  have eq2975 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq2972
       grind)
    | exact superpose eq2972 eq123
    | exact resolve eq123 eq2972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq2980 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq2972
       grind)
    | exact superpose eq2972 eq53
    | exact resolve eq53 eq2972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2972
  have eq2987 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq252 eq2980
    | exact resolve eq2980 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq2980
  have eq2989 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq2975
    | exact resolve eq2975 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975
  have eq2992 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq2987
       grind)
    | exact superpose eq2987 eq53
    | exact resolve eq53 eq2987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2987
  have eq2999 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2992
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2992
    | exact resolve eq2992 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2992
  have eq3008 : (σ x) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2989 eq2952
    | exact resolve eq2952 eq2989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2952 eq2989
  have eq3027 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq2999 eq50
    | exact resolve eq50 eq2999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq3035 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq2999 eq3027
    | exact resolve eq3027 eq2999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2999 eq3027
  have eq3132 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq3035
       grind)
    | exact superpose eq3035 eq122
    | exact resolve eq122 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq3035
  have eq3146 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq3132
    | exact resolve eq3132 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3132
  have eq3157 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3146 eq53
    | exact resolve eq53 eq3146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq3146
  have eq3163 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3008 eq3157
    | exact resolve eq3157 eq3008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008 eq3157
  have eq3167 : False := by grind
  exact eq3167

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_x_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq322 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq326 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq322 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322
  have eq327 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq325 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq325 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq325 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq340 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq327 (σ X0)
       grind)
    | exact superpose eq327 eq15
    | exact resolve eq15 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq340 X0
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq340
    | exact resolve eq340 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327 eq340
  have eq410 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq326 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq739 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq738 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq751 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq739 X1 (τ X0)
       grind)
    | exact superpose eq739 eq18
    | (have j1 := eq739 X1 (τ X0)
       grind)
    | exact resolve eq18 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq754 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq739 (σ X1) (σ X0)
       grind)
    | exact superpose eq739 eq15
    | (have j1 := eq739 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq1047 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq751 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq751
    | exact resolve eq751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq1111 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1047 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1047
    | (have j0 := eq1047 X0 X1
       grind)
    | exact resolve eq1047 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq2736 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq754 x y
       grind)
    | exact superpose eq754 eq16
    | (have j1 := eq754 x y
       grind)
    | exact resolve eq16 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2782 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq754 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq3071 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2736
       have i₂ := eq1111 x y
       grind)
    | exact superpose eq1111 eq2736
    | (have j1 := eq1111 (σ x) (σ y)
       grind)
    | (have r₁ := eq2736
       have r₂ := eq1111 x y
       grind)
    | exact resolve eq2736 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2736
  have eq3072 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3071
  have eq3076 : y ≠ y ∨ x = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3072
       grind)
    | exact superpose eq3072 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3072
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3072
       grind)
    | exact resolve eq13 eq3072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3072
  have eq3086 : y = (k y x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3076
  have eq5390 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2782 x y
       have i₂ := eq3086
       grind)
    | exact superpose eq3086 eq2782
    | (have j0 := eq2782 x y
       grind)
    | exact resolve eq2782 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2782 eq3086
  have eq5397 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq5390
  have eq5398 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq5397
  have eq5573 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5398
       grind)
    | exact superpose eq5398 eq16
    | exact resolve eq16 eq5398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5575 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq5398
       grind)
    | exact superpose eq5398 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq5398
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq5398
       grind)
    | exact resolve eq13 eq5398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5398
  have eq5587 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq5575
  have eq5590 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5587
       have i₂ := eq359 x
       grind)
    | exact superpose eq359 eq5587
    | exact resolve eq5587 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq5587
  have eq5593 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5590
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5590
    | exact resolve eq5590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5590
  have eq8972 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1111 x y
       have i₂ := eq5593
       grind)
    | exact superpose eq5593 eq1111
    | (have j0 := eq1111 x y
       grind)
    | exact resolve eq1111 eq5593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111 eq5593
  have eq9034 : y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq8972
       have r₂ := eq5573
       grind)
    | exact resolve eq8972 eq5573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8972
  have eq9066 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5573
       have i₂ := eq9034
       grind)
    | exact superpose eq9034 eq5573
    | exact resolve eq5573 eq9034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5573 eq9034
  have eq9086 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq9066
  have eq9087 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq9086
  have eq9100 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq9087
       grind)
    | exact superpose eq9087 eq10
    | exact resolve eq10 eq9087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9087
  have eq9173 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9100
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9100
    | exact resolve eq9100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9100
  have eq9174 : x = (M.op x x) := by grind
  clear eq9173
  have eq9193 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq9174
       grind)
    | exact superpose eq9174 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq9174
       grind)
    | exact resolve eq12 eq9174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9197 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq410 x X0
       have i₂ := eq9174
       grind)
    | exact superpose eq9174 eq410
    | (have j0 := eq410 x X0
       grind)
    | exact resolve eq410 eq9174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq9174
  have eq9241 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq9197 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9197
  have eq9242 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq9193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9193
  have eq9527 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq9241 (σ X0)
       grind)
    | exact superpose eq9241 eq15
    | exact resolve eq15 eq9241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9241
  have eq9560 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq9527 X0
       have i₂ := eq9242 X0
       grind)
    | exact superpose eq9242 eq9527
    | exact resolve eq9527 eq9242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9242 eq9527
  have eq10143 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9560 y
       grind)
    | exact superpose eq9560 eq16
    | (have r₁ := eq16
       have r₂ := eq9560 y
       grind)
    | exact resolve eq16 eq9560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9560
  have eq10222 : False := by grind
  exact eq10222

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pxy_pyx_Equation4209 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq109 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq109 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq109
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
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
  have eq960 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq983 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq960 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq960
    | (have j0 := eq960 X0 X1
       grind)
    | exact resolve eq960 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq4087 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq983 x y
       grind)
    | exact superpose eq983 eq16
    | (have j1 := eq983 x y
       grind)
    | exact resolve eq16 eq983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq14660 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq957 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq957
    | exact resolve eq957 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq14802 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14660 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq14660
    | (have j0 := eq14660 X0 X1
       grind)
    | exact resolve eq14660 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14660
  have eq27186 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq4087
       have i₂ := eq14802 x y
       grind)
    | exact superpose eq14802 eq4087
    | (have j1 := eq14802 x y
       grind)
    | (have r₁ := eq4087
       have r₂ := eq14802 x y
       grind)
    | (have r₁ := eq4087
       have r₂ := eq14802 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4087
       have r₂ := eq14802 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4087 eq14802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14802
  have eq27187 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by grind
  clear eq27186
  have eq57736 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27187
       grind)
    | exact superpose eq27187 eq16
    | exact resolve eq16 eq27187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27187
  have eq57737 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq57736
       have r₂ := eq22 x
       grind)
    | exact resolve eq57736 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57736
  have eq57742 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq819 y (σ x)
       have i₂ := eq57737
       grind)
    | exact superpose eq57737 eq819
    | (have j0 := eq819 x (σ y)
       grind)
    | (have r₁ := eq819 y (σ x)
       have r₂ := eq57737
       grind)
    | exact resolve eq819 eq57737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq57747 : (M.op (σ x) (σ y)) = (M.op (σ (M.op y y)) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq109 (σ y) (σ x)
       have i₂ := eq57737
       grind)
    | exact superpose eq57737 eq109
    | exact resolve eq109 eq57737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57737
  have eq57804 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq57742
  have eq57805 : (σ x) = (σ y) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq57804
  have eq57836 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq57747
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq57747
    | exact resolve eq57747 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57747
  have eq57838 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq57805
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq57805
    | exact resolve eq57805 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57805
  have eq57866 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq57838
       grind)
    | exact superpose eq57838 eq10
    | exact resolve eq10 eq57838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57838
  have eq58061 : x = y ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq57866
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq57866
    | exact resolve eq57866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57866
  have eq58063 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58061
       grind)
    | exact superpose eq58061 eq16
    | exact resolve eq16 eq58061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58061
  have eq58064 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq58063
       have r₂ := eq22 x
       grind)
    | exact resolve eq58063 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58063
  have eq58073 : (k y x) = (τ (σ (M.op y y))) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq58064
       grind)
    | exact superpose eq58064 eq10
    | exact resolve eq10 eq58064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58064
  have eq58273 : (k y x) = (M.op y y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq58073
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq58073
    | exact resolve eq58073 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58073
  have eq58277 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (M.op y x) ∨ x = y ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq58273
       grind)
    | exact superpose eq58273 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq58273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58273
  have eq58318 : x = y ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq58277
  have eq58320 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58318
       grind)
    | exact superpose eq58318 eq16
    | exact resolve eq16 eq58318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58318
  have eq58321 : (M.op y y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq58320
       have r₂ := eq22 x
       grind)
    | exact resolve eq58320 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58320
  have eq58432 : (M.op y x) = (M.op (M.op y x) y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq109 y y
       have i₂ := eq58321
       grind)
    | exact superpose eq58321 eq109
    | exact resolve eq109 eq58321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58486 : (M.op x y) ≠ (M.op y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq58321
  have eq58487 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq58432
       have i₂ := eq109 y x
       grind)
    | exact superpose eq109 eq58432
    | exact resolve eq58432 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58432
  have eq58488 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq58487
       have r₂ := eq58486
       grind)
    | exact resolve eq58487 eq58486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58486 eq58487
  have eq58490 : ∀ X0 : G, (M.op x y) ≠ (M.op y X0) ∨ y = X0 ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq58488
       grind)
    | exact superpose eq58488 eq13
    | (have j0 := eq13 y X0
       grind)
    | exact resolve eq13 eq58488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58493 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq110 y
       have i₂ := eq58488
       grind)
    | exact superpose eq58488 eq110
    | exact resolve eq110 eq58488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq81470 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57836
       grind)
    | exact superpose eq57836 eq16
    | exact resolve eq16 eq57836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57836
  have eq81598 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq81470
       have i₂ := eq58488
       grind)
    | exact superpose eq58488 eq81470
    | exact resolve eq81470 eq58488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81470
  have eq81599 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq81598
  have eq81652 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq81599
       have i₂ := eq58488
       grind)
    | exact superpose eq58488 eq81599
    | exact resolve eq81599 eq58488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81599
  have eq81673 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq58490 x
       have i₂ := eq81652
       grind)
    | exact superpose eq81652 eq58490
    | (have j0 := eq58490 x
       grind)
    | (have r₁ := eq58490 x
       have r₂ := eq81652
       grind)
    | exact resolve eq58490 eq81652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58490 eq81652
  have eq81730 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq81673
  have eq81741 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4087
       have i₂ := eq81730
       grind)
    | exact superpose eq81730 eq4087
    | exact resolve eq4087 eq81730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4087 eq81730
  have eq81760 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq81741
  have eq81761 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq81760
  have eq81764 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq81761
       have i₂ := eq58488
       grind)
    | exact superpose eq58488 eq81761
    | exact resolve eq81761 eq58488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58488 eq81761
  have eq84867 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq109 (σ y) (σ x)
       have i₂ := eq81764
       grind)
    | exact superpose eq81764 eq109
    | exact resolve eq109 eq81764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq81764
  have eq84960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq84867
       have i₂ := eq58493
       grind)
    | exact superpose eq58493 eq84867
    | exact resolve eq84867 eq58493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58493 eq84867
  have eq84982 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq84960
       have r₂ := eq16
       grind)
    | exact resolve eq84960 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84960
  have eq84992 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84982
       grind)
    | exact superpose eq84982 eq16
    | exact resolve eq16 eq84982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84982
  have eq85061 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq84992
       have r₂ := eq22 x
       grind)
    | exact resolve eq84992 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84992
  have eq85062 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85061
       grind)
    | exact superpose eq85061 eq16
    | exact resolve eq16 eq85061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85089 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq85061
       grind)
    | exact superpose eq85061 eq10
    | exact resolve eq10 eq85061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85061
  have eq85332 : x = y := by
    first
    | (have i₁ := eq85089
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq85089
    | exact resolve eq85089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85089
  have eq85333 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq85062
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq85062
    | exact resolve eq85062 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq85062
  have eq85339 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq85333
       have i₂ := eq85332
       grind)
    | exact superpose eq85332 eq85333
    | exact resolve eq85333 eq85332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85332 eq85333
  have eq85340 : False := by grind
  exact eq85340

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pyx_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq72 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq72 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq72 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq72 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq44
    | exact resolve eq44 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq75 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq15
    | exact resolve eq15 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq73 (σ X0)
       grind)
    | exact superpose eq73 eq75
    | exact resolve eq75 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq73 (τ X0)
       grind)
    | exact superpose eq73 eq74
    | exact resolve eq74 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq74
  have eq81 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq156 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq16
    | (have j1 := eq81 x y
       grind)
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq230 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op y x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq156
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq156
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq156
       have r₂ := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq156 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq230
  have eq1308 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op y x) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq77 (σ y)
       have i₂ := eq231
       grind)
    | exact superpose eq231 eq77
    | exact resolve eq77 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq1321 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ y = (M.op y x) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1308
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1308
    | exact resolve eq1308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1351 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y x) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1321
       have i₂ := eq77 (σ x)
       grind)
    | exact superpose eq77 eq1321
    | exact resolve eq1321 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1352 : (M.op x x) = (M.op y y) ∨ y = (M.op y x) ∨ (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1351
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1351
    | exact resolve eq1351 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq1353 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq1352
  have eq1357 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq1353
       grind)
    | exact superpose eq1353 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1353
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1353
       grind)
    | exact resolve eq12 eq1353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1381 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq1357
  have eq1426 : (M.op x x) = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1381
       have r₂ := eq156
       grind)
    | exact resolve eq1381 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156 eq1381
  have eq1454 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq76 y
       have i₂ := eq1426
       grind)
    | exact superpose eq1426 eq76
    | exact resolve eq76 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1457 : y = (M.op y x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1454
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq1454
    | exact resolve eq1454 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1580 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1457
       grind)
    | exact superpose eq1457 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1457
       grind)
    | exact resolve eq12 eq1457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq1604 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq1580
  have eq1674 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq1604
       grind)
    | exact superpose eq1604 eq15
    | exact resolve eq15 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1909 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq16
    | exact resolve eq16 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq1923 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1909
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq1909
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq1909
       have r₂ := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq1909 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1924 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1923
  have eq1925 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq1924
  have eq1929 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq1925
       grind)
    | exact superpose eq1925 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1925
       grind)
    | exact resolve eq12 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq1955 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
  clear eq1929
  have eq1974 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq1955
       have r₂ := eq1909
       grind)
    | exact resolve eq1955 eq1909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909 eq1955
  have eq1976 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq77 (σ y)
       have i₂ := eq1974
       grind)
    | exact superpose eq1974 eq77
    | exact resolve eq77 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1979 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 ∨ (M.op X0 X0) ≠ (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0
       have i₂ := eq1974
       grind)
    | exact superpose eq1974 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1974
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1974
       grind)
    | exact resolve eq13 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1980 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (M.op (σ x) (σ x))))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ y)
       have i₂ := eq1974
       grind)
    | exact superpose eq1974 eq9
    | exact resolve eq9 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2017 : (M.op y y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1976
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1976
    | exact resolve eq1976 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq2020 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq2017
       have i₂ := eq77 (σ x)
       grind)
    | exact superpose eq77 eq2017
    | exact resolve eq2017 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq2021 : (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq2020
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2020
    | exact resolve eq2020 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2030 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = X0 ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq2021
       grind)
    | exact superpose eq2021 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2021
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2021
       grind)
    | exact resolve eq13 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2031 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 y
       have i₂ := eq2021
       grind)
    | exact superpose eq2021 eq9
    | exact resolve eq9 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2498 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq2030 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030
  have eq2507 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15 y x
       have i₂ := eq2498
       grind)
    | exact superpose eq2498 eq15
    | exact resolve eq15 eq2498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2498
  have eq2519 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2507
       grind)
    | exact superpose eq2507 eq16
    | exact resolve eq16 eq2507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq3366 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2519
       have i₂ := eq1979 (σ x)
       grind)
    | exact superpose eq1979 eq2519
    | (have j1 := eq1979 (σ x)
       grind)
    | (have r₁ := eq2519
       have r₂ := eq1979 (σ x)
       grind)
    | exact resolve eq2519 eq1979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979 eq2519
  have eq3371 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3366
  have eq3376 : ∀ X0 : G, x = (M.op x y) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ x)
       have i₂ := eq3371
       grind)
    | exact superpose eq3371 eq9
    | exact resolve eq9 eq3371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3371
  have eq3440 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X1 (σ x)))) ∨ y = (M.op y (M.op y (M.op X0 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq3376 X1
       grind)
    | exact superpose eq3376 eq9
    | (have j1 := eq3376 X1
       grind)
    | exact resolve eq9 eq3376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq3551 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y (M.op y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq1980 (σ y)
       have i₂ := eq3440 X0 (σ x)
       grind)
    | exact superpose eq3440 eq1980
    | (have j1 := eq3440 X0 x
       grind)
    | exact resolve eq1980 eq3440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980 eq3440
  have eq3638 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y (M.op y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq3551 X0
       have i₂ := eq1974
       grind)
    | exact superpose eq1974 eq3551
    | (have j0 := eq3551 X0
       grind)
    | exact resolve eq3551 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974 eq3551
  have eq3655 : ∀ X0 : G, y = (τ (M.op (σ x) (σ x))) ∨ y = (M.op y (M.op y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq3638 X0
       grind)
    | exact superpose eq3638 eq10
    | (have j1 := eq3638 X0
       grind)
    | exact resolve eq10 eq3638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq3656 : ∀ X0 : G, y = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op y (M.op y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq3655 X0
       have i₂ := eq77 (σ x)
       grind)
    | exact superpose eq77 eq3655
    | (have j0 := eq3655 X0
       grind)
    | exact resolve eq3655 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq3655
  have eq3668 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op y (M.op y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq3656 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3656
    | (have j0 := eq3656 X0
       grind)
    | exact resolve eq3656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3656
  have eq3677 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op X1 x))) ∨ y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2031 X0
       have i₂ := eq3668 X1
       grind)
    | exact superpose eq3668 eq2031
    | (have j1 := eq3668 X1
       grind)
    | exact resolve eq2031 eq3668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3692 : ∀ X0 X1 : G, x = (M.op x (M.op x (M.op X0 y))) ∨ y = (M.op y (M.op y (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 x
       have i₂ := eq3668 X1
       grind)
    | exact superpose eq3668 eq9
    | (have j1 := eq3668 X1
       grind)
    | exact resolve eq9 eq3668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668
  have eq3754 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq2031 y
       have i₂ := eq3677 X0 x
       grind)
    | exact superpose eq3677 eq2031
    | (have j1 := eq3677 X0 x
       grind)
    | exact resolve eq2031 eq3677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3677
  have eq3834 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq3754 X0
       have i₂ := eq2021
       grind)
    | exact superpose eq2021 eq3754
    | (have j0 := eq3754 X0
       grind)
    | exact resolve eq3754 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754
  have eq3840 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ y = (M.op y (M.op y (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2031 X0
       have i₂ := eq3834 X1
       grind)
    | exact superpose eq3834 eq2031
    | (have j1 := eq3834 X0
       grind)
    | exact resolve eq2031 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834
  have eq3942 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 x))) ∨ x = (M.op x (M.op x (M.op x x))) := by
    intro X0
    first
    | (have i₁ := eq3692 y X0
       have i₂ := eq2021
       grind)
    | exact superpose eq2021 eq3692
    | (have j0 := eq3692 X0 X0
       grind)
    | exact resolve eq3692 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3692
  have eq4012 : y = (M.op y y) ∨ x = (M.op x (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq2031 y
       have i₂ := eq3942 x
       grind)
    | exact superpose eq3942 eq2031
    | exact resolve eq2031 eq3942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2031
  have eq4082 : y = (M.op x x) ∨ x = (M.op x (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq4012
       have i₂ := eq2021
       grind)
    | exact superpose eq2021 eq4012
    | exact resolve eq4012 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4012
  have eq4097 : y = (M.op y (M.op y y)) ∨ x = (M.op x (M.op x (M.op x x))) ∨ x = (M.op x (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq3942 x
       have i₂ := eq4082
       grind)
    | exact superpose eq4082 eq3942
    | exact resolve eq3942 eq4082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3942 eq4082
  have eq4133 : y = (M.op y (M.op y y)) ∨ x = (M.op x (M.op x (M.op x x))) := by grind
  clear eq4097
  have eq4137 : y = (M.op y (M.op x x)) ∨ x = (M.op x (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq4133
       have i₂ := eq2021
       grind)
    | exact superpose eq2021 eq4133
    | exact resolve eq4133 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133
  have eq4154 : x = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x (M.op x x))) := by
    first
    | (have i₁ := eq9 x y x
       have i₂ := eq4137
       grind)
    | exact superpose eq4137 eq9
    | exact resolve eq9 eq4137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq4528 : ∀ X0 : G, y ≠ y ∨ y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have j0 := eq3840 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3840
  have eq4529 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have j0 := eq4528 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4528
  have eq4535 : y = (M.op y y) := by
    first
    | (have i₁ := eq9 y y x
       have i₂ := eq4529 x
       grind)
    | exact superpose eq4529 eq9
    | exact resolve eq9 eq4529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4529
  have eq4638 : y = (M.op x x) := by
    first
    | (have i₁ := eq2021
       have i₂ := eq4535
       grind)
    | exact superpose eq4535 eq2021
    | exact resolve eq2021 eq4535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021 eq4535
  have eq4973 : x = (M.op x (M.op x y)) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq4154
       have i₂ := eq4638
       grind)
    | exact superpose eq4638 eq4154
    | exact resolve eq4154 eq4638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4154
  have eq5101 : x = (M.op x (M.op x y)) := by grind
  clear eq4973
  have eq5449 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq76 x
       have i₂ := eq4638
       grind)
    | exact superpose eq4638 eq76
    | exact resolve eq76 eq4638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5451 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 x
       have i₂ := eq4638
       grind)
    | exact superpose eq4638 eq9
    | exact resolve eq9 eq4638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5714 : (σ (M.op x y)) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5449
       grind)
    | exact superpose eq5449 eq16
    | exact resolve eq16 eq5449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7501 : x = (M.op x x) := by
    first
    | (have i₁ := eq5451 x
       have i₂ := eq5101
       grind)
    | exact superpose eq5101 eq5451
    | exact resolve eq5451 eq5101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101 eq5451
  have eq7557 : x = y := by
    first
    | (have i₁ := eq4638
       have i₂ := eq7501
       grind)
    | exact superpose eq7501 eq4638
    | exact resolve eq4638 eq7501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4638 eq7501
  have eq7995 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5449
       have i₂ := eq7557
       grind)
    | exact superpose eq7557 eq5449
    | exact resolve eq5449 eq7557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5449
  have eq8027 : (σ (M.op x x)) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5714
       have i₂ := eq7557
       grind)
    | exact superpose eq7557 eq5714
    | exact resolve eq5714 eq7557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5714 eq7557
  have eq8471 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq8027
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq8027
    | exact resolve eq8027 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq8027
  have eq8934 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8471
       have i₂ := eq7995
       grind)
    | exact superpose eq7995 eq8471
    | exact resolve eq8471 eq7995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8471
  have eq9121 : False := by grind
  exact eq9121

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 X1
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq30
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq30 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq3805 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) X0
       have i₂ := eq82 X1 X0
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 (σ X1) X0
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) X1
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq82 X0 (σ X0)
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq3833 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) ∨ (M.op (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq3805 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805
  have eq67470 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) X1)
       have i₂ := eq3833 X1 X0
       grind)
    | exact superpose eq3833 eq11
    | (have j1 := eq3833 X1 X0
       grind)
    | exact resolve eq11 eq3833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833
  have eq67603 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67470 X0 X1
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq67470
    | (have j0 := eq67470 X0 X1
       grind)
    | exact resolve eq67470 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq67470
  have eq67604 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq67603 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67603
  have eq67687 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq67604 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq67604
    | exact resolve eq67604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67776 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq67604 X0 (σ X1)
       grind)
    | exact superpose eq67604 eq15
    | (have j1 := eq67604 X0 (σ X1)
       grind)
    | exact resolve eq15 eq67604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67604
  have eq68543 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq67687 (τ X0) X1
       grind)
    | exact superpose eq67687 eq17
    | (have j1 := eq67687 (τ X0) X1
       grind)
    | exact resolve eq17 eq67687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq67687
  have eq69780 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68543 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq68543
    | exact resolve eq68543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68543
  have eq70062 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq69780 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq69780
    | (have j0 := eq69780 X0 X1
       grind)
    | exact resolve eq69780 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69780
  have eq112030 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67776 x y
       grind)
    | exact superpose eq67776 eq16
    | (have j1 := eq67776 x y
       grind)
    | exact resolve eq16 eq67776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112189 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67776 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67776
  have eq114512 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq112030
       have i₂ := eq70062 x y
       grind)
    | exact superpose eq70062 eq112030
    | (have j1 := eq70062 (σ x) (σ y)
       grind)
    | (have r₁ := eq112030
       have r₂ := eq70062 x y
       grind)
    | exact resolve eq112030 eq70062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114515 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq114512
  have eq114533 : y ≠ y ∨ y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq114515
       grind)
    | exact superpose eq114515 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq114515
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq114515
       grind)
    | exact resolve eq13 eq114515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114515
  have eq114600 : y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq114533
  have eq130352 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112189 x y
       have i₂ := eq114600
       grind)
    | exact superpose eq114600 eq112189
    | (have j0 := eq112189 x y
       grind)
    | exact resolve eq112189 eq114600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112189 eq114600
  have eq130363 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq130352
  have eq130364 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq130363
  have eq130992 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq130364
       grind)
    | exact superpose eq130364 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq130364
       grind)
    | exact resolve eq12 eq130364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130364
  have eq131062 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq130992
  have eq131066 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112030
       have i₂ := eq131062
       grind)
    | exact superpose eq131062 eq112030
    | exact resolve eq112030 eq131062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112030 eq131062
  have eq131105 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq131066
  have eq131106 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq131105
  have eq131736 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq131106
       grind)
    | exact superpose eq131106 eq16
    | exact resolve eq16 eq131106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131767 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq131106
       grind)
    | exact superpose eq131106 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq131106
       grind)
    | exact resolve eq13 eq131106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131836 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq131767
  have eq131849 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq131836
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq131836
    | exact resolve eq131836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131836
  have eq132489 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq131849
       grind)
    | exact superpose eq131849 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq131849
       grind)
    | exact resolve eq12 eq131849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131849
  have eq132559 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq132489
  have eq132563 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq132559
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq132559
    | exact resolve eq132559 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132559
  have eq132589 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq132563
       have i₂ := eq131106
       grind)
    | exact superpose eq131106 eq132563
    | exact resolve eq132563 eq131106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131106 eq132563
  have eq132590 : (σ y) = (σ (k x y)) := by grind
  clear eq132589
  have eq133231 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70062 x y
       have i₂ := eq132590
       grind)
    | exact superpose eq132590 eq70062
    | (have j0 := eq70062 x y
       grind)
    | exact resolve eq70062 eq132590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70062 eq132590
  have eq133550 : y = (M.op x y) := by
    first
    | (have r₁ := eq133231
       have r₂ := eq131736
       grind)
    | exact resolve eq133231 eq131736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133231
  have eq134048 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq131736
       have i₂ := eq133550
       grind)
    | exact superpose eq133550 eq131736
    | exact resolve eq131736 eq133550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131736 eq133550
  have eq134131 : False := by grind
  exact eq134131

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq70 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq70 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq70 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq70 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq72 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq44 X0 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq44
    | exact resolve eq44 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq15
    | exact resolve eq15 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq73
    | exact resolve eq73 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq71 (τ X0)
       grind)
    | exact superpose eq71 eq72
    | exact resolve eq72 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq72
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ X1) (σ X0)) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq156 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq134
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq134
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq134
       have r₂ := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq134 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq157 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq156
  have eq885 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq75 (σ y)
       have i₂ := eq157
       grind)
    | exact superpose eq157 eq75
    | exact resolve eq75 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq897 : (M.op y y) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq885
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq885
    | exact resolve eq885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq920 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq897
       have i₂ := eq75 (σ x)
       grind)
    | exact superpose eq75 eq897
    | exact resolve eq897 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897
  have eq921 : (M.op y y) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq920
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq920
    | exact resolve eq920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq922 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq921
  have eq937 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq75 (σ x)
       have i₂ := eq922
       grind)
    | exact superpose eq922 eq75
    | exact resolve eq75 eq922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq943 : x = (M.op x x) ∨ x = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq937
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq937
    | exact resolve eq937 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq944 : (M.op y y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq943
  have eq985 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74 y
       have i₂ := eq944
       grind)
    | exact superpose eq944 eq74
    | exact resolve eq74 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq991 : x = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq985
       have i₂ := eq74 x
       grind)
    | exact superpose eq74 eq985
    | exact resolve eq985 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq985
  have eq1078 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq74 x
       have i₂ := eq991
       grind)
    | exact superpose eq991 eq74
    | exact resolve eq74 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1081 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq991
       grind)
    | exact superpose eq991 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq991
       grind)
    | exact resolve eq12 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq1082 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1081 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1168 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (M.op x X0)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq1082 X0
       grind)
    | exact superpose eq1082 eq15
    | exact resolve eq15 eq1082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1082
  have eq1236 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (σ x)
       have i₂ := eq1078
       grind)
    | exact superpose eq1078 eq12
    | (have j0 := eq12 X0 (σ x)
       grind)
    | (have r₁ := eq12 X0 (σ x)
       have r₂ := eq1078
       grind)
    | exact resolve eq12 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1237 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1236 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1529 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1168 y
       grind)
    | exact superpose eq1168 eq16
    | exact resolve eq16 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1534 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq1529
       have r₂ := eq1237 (σ y)
       grind)
    | exact resolve eq1529 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq1529
  have eq1560 : (τ (M.op (σ x) (σ x))) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq75 (σ y)
       have i₂ := eq1534
       grind)
    | exact superpose eq1534 eq75
    | exact resolve eq75 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1563 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (σ y)
       have i₂ := eq1534
       grind)
    | exact superpose eq1534 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1534
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1534
       grind)
    | exact resolve eq13 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1565 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1563 X0
       have i₂ := eq1534
       grind)
    | exact superpose eq1534 eq1563
    | (have j0 := eq1563 X0
       grind)
    | (have r₁ := eq1563 (σ y)
       have r₂ := eq1534
       grind)
    | exact resolve eq1563 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq1567 : (M.op y y) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1560
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1560
    | exact resolve eq1560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq1568 : (M.op y y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq1567
       have i₂ := eq75 (σ x)
       grind)
    | exact superpose eq75 eq1567
    | exact resolve eq1567 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq1569 : (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq1568
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1568
    | exact resolve eq1568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568
  have eq1603 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (M.op y y) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1569
       grind)
    | exact superpose eq1569 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1569
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1569
       grind)
    | exact resolve eq13 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1607 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = (M.op x x) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1603 X0
       have i₂ := eq1569
       grind)
    | exact superpose eq1569 eq1603
    | (have j0 := eq1603 X0
       grind)
    | (have r₁ := eq1603 y
       have r₂ := eq1569
       grind)
    | exact resolve eq1603 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq2099 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq1607 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq2110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq15 x y
       have i₂ := eq2099
       grind)
    | exact superpose eq2099 eq15
    | exact resolve eq15 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099
  have eq2118 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2110
       grind)
    | exact superpose eq2110 eq16
    | exact resolve eq16 eq2110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110
  have eq2985 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq1565 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq2998 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2118
       have i₂ := eq2985
       grind)
    | exact superpose eq2985 eq2118
    | (have r₁ := eq2118
       have r₂ := eq2985
       grind)
    | exact resolve eq2118 eq2985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118 eq2985
  have eq3002 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq2998
  have eq3022 : y = (τ (M.op (σ x) (σ x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3002
       grind)
    | exact superpose eq3002 eq10
    | exact resolve eq10 eq3002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002
  have eq3026 : y = (M.op (τ (σ x)) (τ (σ x))) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3022
       have i₂ := eq75 (σ x)
       grind)
    | exact superpose eq75 eq3022
    | exact resolve eq3022 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq3022
  have eq3037 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3026
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3026
    | exact resolve eq3026 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3038 : y = (M.op x x) := by grind
  clear eq3037
  have eq3066 : y = (M.op y y) := by
    first
    | (have i₁ := eq1569
       have i₂ := eq3038
       grind)
    | exact superpose eq3038 eq1569
    | exact resolve eq1569 eq3038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1569
  have eq3597 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq74 y
       have i₂ := eq3066
       grind)
    | exact superpose eq3066 eq74
    | exact resolve eq74 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3618 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3597
       have i₂ := eq1534
       grind)
    | exact superpose eq1534 eq3597
    | exact resolve eq3597 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534 eq3597
  have eq3822 : (σ (M.op x y)) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3618
       grind)
    | exact superpose eq3618 eq16
    | exact resolve eq16 eq3618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4830 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 x
       have i₂ := eq3038
       grind)
    | exact superpose eq3038 eq9
    | exact resolve eq9 eq3038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4968 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq4830 y
       have i₂ := eq3066
       grind)
    | exact superpose eq3066 eq4830
    | exact resolve eq4830 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3066
  have eq5021 : x = (M.op x x) := by
    first
    | (have i₁ := eq4830 x
       have i₂ := eq4968
       grind)
    | exact superpose eq4968 eq4830
    | exact resolve eq4830 eq4968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830 eq4968
  have eq5087 : x = y := by
    first
    | (have i₁ := eq3038
       have i₂ := eq5021
       grind)
    | exact superpose eq5021 eq3038
    | exact resolve eq3038 eq5021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3038 eq5021
  have eq5403 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3618
       have i₂ := eq5087
       grind)
    | exact superpose eq5087 eq3618
    | exact resolve eq3618 eq5087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3618
  have eq5406 : (σ (M.op x x)) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq3822
       have i₂ := eq5087
       grind)
    | exact superpose eq5087 eq3822
    | exact resolve eq3822 eq5087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3822 eq5087
  have eq5539 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5406
       have i₂ := eq74 x
       grind)
    | exact superpose eq74 eq5406
    | exact resolve eq5406 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq5406
  have eq5923 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5539
       have i₂ := eq5403
       grind)
    | exact superpose eq5403 eq5539
    | exact resolve eq5539 eq5403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5539
  have eq6102 : False := by grind
  exact eq6102
