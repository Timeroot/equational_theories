import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq366 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq87 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq87 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq87 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq380 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq381 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq380 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq383 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq381 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq381
    | (have j0 := eq381 X0 X1
       grind)
    | exact resolve eq381 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq386 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq383 X0 X1
       have j1 := eq377 X1 X0
       grind)
    | (have r₁ := eq383 X1 X0
       have r₂ := eq377 X0 X1
       grind)
    | (have r₁ := eq383 X1 (k X0 X1)
       have r₂ := eq377 X0 X1
       grind)
    | (have r₁ := eq383 X1 X1
       have r₂ := eq377 X1 X1
       grind)
    | exact resolve eq383 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq383
  have eq534 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq386 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq386
    | exact resolve eq386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq386 y x
       grind)
    | exact superpose eq386 eq16
    | (have j1 := eq386 y x
       grind)
    | exact resolve eq16 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq559 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq534 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq534
    | (have j0 := eq534 X0 X1
       grind)
    | exact resolve eq534 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq534
  have eq612 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq559
    | exact resolve eq559 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq695 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq612 (τ X0) X1
       grind)
    | exact superpose eq612 eq18
    | (have j1 := eq612 (τ X0) X1
       grind)
    | exact resolve eq18 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq612
  have eq855 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq695 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq695
    | exact resolve eq695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq903 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq855 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq855
    | (have j0 := eq855 X0 X1
       grind)
    | exact resolve eq855 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq985 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq541
       have i₂ := eq903 x y
       grind)
    | exact superpose eq903 eq541
    | (have j1 := eq903 (σ x) (σ y)
       grind)
    | (have r₁ := eq541
       have r₂ := eq903 x y
       grind)
    | exact resolve eq541 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq986 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq985
  have eq993 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq986
  have eq1059 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq541
       have i₂ := eq993
       grind)
    | exact superpose eq993 eq541
    | exact resolve eq541 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq993
  have eq1060 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1059
  have eq1061 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1060
  have eq1072 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1061
  have eq1085 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1072
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1072
    | exact resolve eq1072 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1171 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1085
       grind)
    | exact superpose eq1085 eq16
    | exact resolve eq16 eq1085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1229 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1171
       have i₂ := eq903 x y
       grind)
    | exact superpose eq903 eq1171
    | (have j1 := eq903 x y
       grind)
    | (have r₁ := eq1171
       have r₂ := eq903 x y
       grind)
    | exact resolve eq1171 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq1230 : x = (M.op y y) := by grind
  clear eq1229
  have eq1236 : (M.op x y) = (k x y) := by grind
  clear eq1230
  have eq1281 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1171
       have i₂ := eq1236
       grind)
    | exact superpose eq1236 eq1171
    | exact resolve eq1171 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171 eq1236
  have eq1284 : False := by grind
  exact eq1284

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq37 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq41 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq362 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq16
    | (have j1 := eq88 x y
       grind)
    | exact resolve eq16 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1427 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq371 (τ X0) (τ X1)
       have i₂ := eq37 X1 X0
       grind)
    | exact superpose eq37 eq371
    | (have j0 := eq371 (τ X0) (τ X1)
       grind)
    | exact resolve eq371 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1450 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1427 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1427
    | (have j0 := eq1427 X0 X1
       grind)
    | exact resolve eq1427 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427
  have eq1460 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1450 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1450
    | (have j0 := eq1450 X0 X1
       grind)
    | exact resolve eq1450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq1469 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1460 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1460
    | (have j0 := eq1460 X0 X1
       grind)
    | exact resolve eq1460 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1477 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1469 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1469
    | (have j0 := eq1469 X0 X1
       grind)
    | exact resolve eq1469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1483 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1477 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1477
    | (have j0 := eq1477 X0 X1
       grind)
    | exact resolve eq1477 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1477
  have eq1486 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1483 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1483
    | (have j0 := eq1483 X0 X1
       grind)
    | exact resolve eq1483 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1483
  have eq4300 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq87 (σ X1) X1
       grind)
    | (have r₁ := eq13 (M.op (σ X1) (σ X1)) X1
       have r₂ := eq87 (M.op (M.op (σ X1) (σ X1)) X1) X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4309 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq87 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq4310 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4309 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309
  have eq4312 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4300 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4300
  have eq4313 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq4312 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4312
  have eq4315 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4310 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4310
    | (have j0 := eq4310 X0
       grind)
    | exact resolve eq4310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4310
  have eq4362 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq4315 X0
       grind)
    | exact superpose eq4315 eq41
    | (have j1 := eq4315 X0
       grind)
    | exact resolve eq41 eq4315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq4315
  have eq4388 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4362 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4362
    | (have j0 := eq4362 X0
       grind)
    | exact resolve eq4362 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4362
  have eq4389 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq4388 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4388
  have eq4392 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4389 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4389
    | exact resolve eq4389 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4415 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq4389 X0
       grind)
    | exact superpose eq4389 eq11
    | exact resolve eq11 eq4389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4476 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4392 X0
       have i₂ := eq37 X0 X0
       grind)
    | exact superpose eq37 eq4392
    | exact resolve eq4392 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4392
  have eq4624 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq4476 X0
       grind)
    | exact superpose eq4476 eq11
    | exact resolve eq11 eq4476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4735 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq4624 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4624
    | exact resolve eq4624 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4624
  have eq4802 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0 X0
       have i₂ := eq4735 (τ X0)
       grind)
    | exact superpose eq4735 eq37
    | exact resolve eq37 eq4735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4856 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4802 X0
       have i₂ := eq4476 X0
       grind)
    | exact superpose eq4476 eq4802
    | exact resolve eq4802 eq4476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4476 eq4802
  have eq5399 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq5436 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq5399 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq5399
    | exact resolve eq5399 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5399
  have eq5478 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5436 X0
       have i₂ := eq4735 X0
       grind)
    | exact superpose eq4735 eq5436
    | exact resolve eq5436 eq4735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5436
  have eq5503 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq5478
  have eq197076 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4313 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4313
    | exact resolve eq4313 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197242 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 (σ X1)
       have i₂ := eq4313 (σ X0) X1
       grind)
    | exact superpose eq4313 eq32
    | (have j1 := eq4313 (σ X0) X1
       grind)
    | exact resolve eq32 eq4313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4313
  have eq197416 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq197242 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq197242
    | (have j0 := eq197242 X0 X1
       grind)
    | exact resolve eq197242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197242
  have eq197540 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq197076 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq197076
    | (have j0 := eq197076 X0 X1
       grind)
    | exact resolve eq197076 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197076
  have eq197604 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq197416 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq197416
    | (have j0 := eq197416 X0 X1
       grind)
    | exact resolve eq197416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197416
  have eq197780 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq197604 X0 X1
       have i₂ := eq4415 X1
       grind)
    | exact superpose eq4415 eq197604
    | (have j0 := eq197604 X0 X1
       grind)
    | exact resolve eq197604 eq4415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197604
  have eq197930 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq197780 X0 X1
       have i₂ := eq4735 X1
       grind)
    | exact superpose eq4735 eq197780
    | (have j0 := eq197780 X0 X1
       grind)
    | exact resolve eq197780 eq4735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197780
  have eq198046 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq197930 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq197930
    | (have j0 := eq197930 X0 X1
       grind)
    | exact resolve eq197930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197930
  have eq198630 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq197540 X1 X0
       grind)
    | exact superpose eq197540 eq11
    | (have j1 := eq197540 X1 X0
       grind)
    | exact resolve eq11 eq197540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197540
  have eq198929 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq198630 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq198630
    | (have j0 := eq198630 X0 X1
       grind)
    | exact resolve eq198630 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198630
  have eq199381 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq198929 X0 (τ X1)
       grind)
    | exact superpose eq198929 eq19
    | (have j1 := eq198929 X0 (τ X1)
       grind)
    | exact resolve eq19 eq198929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq198929
  have eq199732 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq199381 X0 X1
       have i₂ := eq4856 X1
       grind)
    | exact superpose eq4856 eq199381
    | (have j0 := eq199381 X0 X1
       grind)
    | exact resolve eq199381 eq4856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199381
  have eq201714 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq198046 (τ X1) (τ X0)
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq198046
    | (have j0 := eq198046 (τ X0) (τ X1)
       grind)
    | exact resolve eq198046 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq198046
  have eq202286 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq201714 X0 X1
       have i₂ := eq4856 X1
       grind)
    | exact superpose eq4856 eq201714
    | (have j0 := eq201714 X0 X1
       grind)
    | exact resolve eq201714 eq4856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4856 eq201714
  have eq202508 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq202286 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq202286
    | (have j0 := eq202286 X0 X1
       grind)
    | exact resolve eq202286 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202286
  have eq202700 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq202508 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq202508
    | (have j0 := eq202508 X0 X1
       grind)
    | exact resolve eq202508 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202508
  have eq202847 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq202700 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq202700
    | (have j0 := eq202700 X0 X1
       grind)
    | exact resolve eq202700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202700
  have eq202951 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq202847 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq202847
    | (have j0 := eq202847 X0 X1
       grind)
    | exact resolve eq202847 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202847
  have eq203578 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202951 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202951
  have eq211556 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq199732 (τ X0) X1
       grind)
    | exact superpose eq199732 eq18
    | (have j1 := eq199732 (τ X0) X1
       grind)
    | exact resolve eq18 eq199732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq199732
  have eq211688 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211556 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq211556
    | (have j0 := eq211556 X0 X1
       grind)
    | exact resolve eq211556 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211556
  have eq211856 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211688 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq211688
    | (have j0 := eq211688 X0 X1
       grind)
    | exact resolve eq211688 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211688
  have eq212007 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq211856 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq211856
    | (have j0 := eq211856 X0 X1
       grind)
    | exact resolve eq211856 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211856
  have eq225451 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) (τ (σ X1)))) ∨ (τ (σ X0)) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq212007 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq212007
    | (have j0 := eq212007 (σ X0) (σ X1)
       grind)
    | exact resolve eq212007 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212007
  have eq226136 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (τ (σ X0)) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq225451 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq225451
    | (have j0 := eq225451 X0 X1
       grind)
    | exact resolve eq225451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225451
  have eq226394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (τ (σ X0)) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq226136 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq226136
    | (have j0 := eq226136 X0 X1
       grind)
    | exact resolve eq226136 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226136
  have eq226575 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226394 X0 X1
       have i₂ := eq4389 X1
       grind)
    | exact superpose eq4389 eq226394
    | (have j0 := eq226394 X0 X1
       grind)
    | exact resolve eq226394 eq4389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4389 eq226394
  have eq226717 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226575 X0 X1
       have i₂ := eq4735 X1
       grind)
    | exact superpose eq4735 eq226575
    | (have j0 := eq226575 X0 X1
       grind)
    | exact resolve eq226575 eq4735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226575
  have eq226833 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq226717 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq226717
    | (have j0 := eq226717 X0 X1
       grind)
    | exact resolve eq226717 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226717
  have eq228452 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq362
       have i₂ := eq226833 x y
       grind)
    | exact superpose eq226833 eq362
    | (have j1 := eq226833 x y
       grind)
    | (have r₁ := eq362
       have r₂ := eq226833 x y
       grind)
    | exact resolve eq362 eq226833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq226833
  have eq228649 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq228452
  have eq228744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq371 x y
       grind)
    | (have r₁ := eq228649
       have r₂ := eq371 x y
       grind)
    | exact resolve eq228649 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq228649
  have eq228940 : (σ x) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq228744
       have i₂ := eq4415 y
       grind)
    | exact superpose eq4415 eq228744
    | exact resolve eq228744 eq4415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228744
  have eq229087 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq228940
       have i₂ := eq4735 y
       grind)
    | exact superpose eq4735 eq228940
    | exact resolve eq228940 eq4735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228940
  have eq232607 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq229087
       grind)
    | exact superpose eq229087 eq16
    | exact resolve eq16 eq229087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232640 : (τ (σ x)) ≠ (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ x)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq203578 (σ x) (σ y)
       have i₂ := eq229087
       grind)
    | exact superpose eq229087 eq203578
    | (have j0 := eq203578 (σ x) (σ y)
       grind)
    | exact resolve eq203578 eq229087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203578 eq229087
  have eq232643 : (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ x)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq232640
  have eq232648 : (σ x) = (σ (k y y)) ∨ (τ (σ x)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq232643
       have i₂ := eq4415 y
       grind)
    | exact superpose eq4415 eq232643
    | exact resolve eq232643 eq4415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4415 eq232643
  have eq232659 : (σ x) = (σ (M.op y y)) ∨ (τ (σ x)) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq232648
       have i₂ := eq4735 y
       grind)
    | exact superpose eq4735 eq232648
    | exact resolve eq232648 eq4735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4735 eq232648
  have eq232660 : (σ x) = (σ (M.op y y)) ∨ (τ (σ x)) = (τ (k (σ x) (σ y))) ∨ x = (M.op y y) := by grind
  clear eq232659
  have eq232665 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq232660
       have i₂ := eq26 (σ x) y
       grind)
    | exact superpose eq26 eq232660
    | exact resolve eq232660 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq232660
  have eq232668 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq232665
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq232665
    | exact resolve eq232665 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232665
  have eq233675 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1486 x y
       have i₂ := eq232668
       grind)
    | exact superpose eq232668 eq1486
    | (have j0 := eq1486 x y
       grind)
    | (have r₁ := eq1486 x y
       have r₂ := eq232668
       grind)
    | exact resolve eq1486 eq232668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486 eq232668
  have eq233697 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq233675
  have eq233698 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq233697
  have eq234761 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq232607
       have i₂ := eq233698
       grind)
    | exact superpose eq233698 eq232607
    | exact resolve eq232607 eq233698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232607 eq233698
  have eq234762 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq234761
  have eq234763 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq234762
  have eq234904 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq234763
       grind)
    | exact superpose eq234763 eq10
    | exact resolve eq10 eq234763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234763
  have eq235208 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq234904
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq234904
    | exact resolve eq234904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234904
  have eq235209 : x = (M.op y y) := by grind
  clear eq235208
  have eq236423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5503 y
       have i₂ := eq235209
       grind)
    | exact superpose eq235209 eq5503
    | exact resolve eq5503 eq235209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5503 eq235209
  have eq236769 : False := by grind
  exact eq236769

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq376 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq87 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq380 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq376 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq381 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq380 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq383 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq381 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq381
    | (have j0 := eq381 X0 X1
       grind)
    | exact resolve eq381 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq387 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq383 X0 X1
       have j1 := eq379 X0 X1
       grind)
    | (have r₁ := eq383 X0 X1
       have r₂ := eq379 X0 X1
       grind)
    | (have r₁ := eq383 X0 (k X1 X0)
       have r₂ := eq379 X0 X1
       grind)
    | (have r₁ := eq383 X0 X0
       have r₂ := eq379 X0 X0
       grind)
    | exact resolve eq383 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq383
  have eq530 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq387 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq387
    | exact resolve eq387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq387 x y
       grind)
    | exact superpose eq387 eq16
    | (have j1 := eq387 x y
       grind)
    | exact resolve eq16 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq561 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq530
    | (have j0 := eq530 X0 X1
       grind)
    | exact resolve eq530 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq530
  have eq613 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq561 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq561
    | exact resolve eq561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq696 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq613 (τ X1) X0
       grind)
    | exact superpose eq613 eq18
    | (have j1 := eq613 (τ X1) X0
       grind)
    | exact resolve eq18 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq613
  have eq854 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq696
    | exact resolve eq696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq901 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq854 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq854
    | (have j0 := eq854 X0 X1
       grind)
    | exact resolve eq854 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq1017 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq542
       have i₂ := eq901 y x
       grind)
    | exact superpose eq901 eq542
    | (have j1 := eq901 (σ y) (σ x)
       grind)
    | (have r₁ := eq542
       have r₂ := eq901 y x
       grind)
    | exact resolve eq542 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1017
  have eq1023 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1018
  have eq1037 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq542
       have i₂ := eq1023
       grind)
    | exact superpose eq1023 eq542
    | exact resolve eq542 eq1023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542 eq1023
  have eq1038 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1037
  have eq1039 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1038
  have eq1050 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1039
  have eq1062 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1050
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1050
    | exact resolve eq1050 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1148 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1062
       grind)
    | exact superpose eq1062 eq16
    | exact resolve eq16 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1192 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1148
       have i₂ := eq901 y x
       grind)
    | exact superpose eq901 eq1148
    | (have j1 := eq901 y x
       grind)
    | (have r₁ := eq1148
       have r₂ := eq901 y x
       grind)
    | exact resolve eq1148 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq1193 : y = (M.op x x) := by grind
  clear eq1192
  have eq1199 : (M.op x y) = (k y x) := by grind
  clear eq1193
  have eq1266 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1148
       have i₂ := eq1199
       grind)
    | exact superpose eq1199 eq1148
    | exact resolve eq1148 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq1199
  have eq1269 : False := by grind
  exact eq1269

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq56 (τ X1) X0
       grind)
    | exact superpose eq56 eq17
    | (have j1 := eq56 (τ X1) X0
       grind)
    | exact resolve eq17 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq132 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq67 X0 X0
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq67 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq67 X0 X0
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq141 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq138 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq138 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq245 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq71
    | exact resolve eq71 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq267 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq245 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq245
    | (have j0 := eq245 X0 X1
       grind)
    | exact resolve eq245 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq278 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq267 X0 X0
       grind)
    | exact superpose eq267 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq267 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq267 X0 X0
       grind)
    | exact resolve eq12 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq278 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq132
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq132
    | (have j1 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq132 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq326 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq325
  have eq328 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq326
       grind)
    | exact superpose eq326 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq326
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq326
       grind)
    | exact resolve eq13 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq330 : x = (k y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq328
  have eq978 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq294 X0 X1
       grind)
    | exact superpose eq294 eq10
    | (have j1 := eq294 X0 X1
       grind)
    | exact resolve eq10 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq1019 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq978 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq978
    | (have j0 := eq978 X0 X0
       grind)
    | exact resolve eq978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq1090 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1019 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1091 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1090 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1154 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 X1
       have i₂ := eq1091 X0
       grind)
    | exact superpose eq1091 eq141
    | (have j0 := eq141 X0 X1
       grind)
    | exact resolve eq141 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq1170 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1091 (σ X0)
       grind)
    | exact superpose eq1091 eq15
    | exact resolve eq15 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1189 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1170 X0
       have i₂ := eq1091 X0
       grind)
    | exact superpose eq1091 eq1170
    | exact resolve eq1170 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq1170
  have eq20282 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq140 x y
       have i₂ := eq330
       grind)
    | exact superpose eq330 eq140
    | (have j0 := eq140 x y
       grind)
    | exact resolve eq140 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq330
  have eq20297 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq20282
  have eq20298 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq20297
  have eq20305 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20298
       grind)
    | exact superpose eq20298 eq16
    | exact resolve eq16 eq20298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20298
  have eq20461 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq20305
       have i₂ := eq267 y x
       grind)
    | exact superpose eq267 eq20305
    | (have j1 := eq267 x x
       grind)
    | exact resolve eq20305 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20305
  have eq20462 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ (k y x)) := by grind
  clear eq20461
  have eq20466 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq20462
       grind)
    | exact superpose eq20462 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq20462
       grind)
    | exact resolve eq12 eq20462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20462
  have eq20562 : ∀ X0 : G, (M.op x X0) = (k X0 x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    intro X0
    first
    | (have j0 := eq20466 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20466
  have eq20628 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq132
       have i₂ := eq20562 y
       grind)
    | exact superpose eq20562 eq132
    | (have r₁ := eq132
       have r₂ := eq20562 x
       grind)
    | exact resolve eq132 eq20562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20562
  have eq20629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (k y x)) := by grind
  clear eq20628
  have eq20630 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20629
       have r₂ := eq132
       grind)
    | exact resolve eq20629 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq20629
  have eq20759 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20630
       grind)
    | exact superpose eq20630 eq16
    | exact resolve eq16 eq20630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20762 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq20630
       grind)
    | exact superpose eq20630 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20630
       grind)
    | exact resolve eq13 eq20630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20630
  have eq20781 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
  clear eq20762
  have eq20784 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq20781
       have i₂ := eq1189 x
       grind)
    | exact superpose eq1189 eq20781
    | exact resolve eq20781 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189 eq20781
  have eq20785 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq20784
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20784
    | exact resolve eq20784 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20784
  have eq20788 : (σ x) ≠ (σ x) ∨ (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq20759
       have i₂ := eq267 y x
       grind)
    | exact superpose eq267 eq20759
    | (have j1 := eq267 y x
       grind)
    | exact resolve eq20759 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq20789 : (σ (M.op x y)) = (σ (k y x)) := by grind
  clear eq20788
  have eq23174 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq20785
       have i₂ := eq20789
       grind)
    | exact superpose eq20789 eq20785
    | exact resolve eq20785 eq20789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20785 eq20789
  have eq23175 : (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq23174
       have r₂ := eq20759
       grind)
    | exact resolve eq23174 eq20759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759 eq23174
  have eq23363 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq1154 x X0
       have i₂ := eq23175
       grind)
    | exact superpose eq23175 eq1154
    | (have j0 := eq1154 x X0
       grind)
    | (have r₁ := eq1154 x x
       have r₂ := eq23175
       grind)
    | exact resolve eq1154 eq23175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154
  have eq23396 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq23175
       grind)
    | exact superpose eq23175 eq10
    | exact resolve eq10 eq23175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23175
  have eq23509 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq23363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23363
  have eq23526 : x = (M.op x x) := by
    first
    | (have i₁ := eq23396
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23396
    | exact resolve eq23396 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23396
  have eq23533 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq23526
       grind)
    | exact superpose eq23526 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq23526
       grind)
    | exact resolve eq12 eq23526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23526
  have eq23641 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq23533 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23533
  have eq23903 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23509 (σ X0)
       grind)
    | exact superpose eq23509 eq15
    | exact resolve eq15 eq23509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23509
  have eq23978 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq23903 X0
       have i₂ := eq23641 X0
       grind)
    | exact superpose eq23641 eq23903
    | exact resolve eq23903 eq23641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23641 eq23903
  have eq27790 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23978 y
       grind)
    | exact superpose eq23978 eq16
    | (have r₁ := eq16
       have r₂ := eq23978 y
       grind)
    | exact resolve eq16 eq23978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23978
  have eq27960 : False := by grind
  exact eq27960
