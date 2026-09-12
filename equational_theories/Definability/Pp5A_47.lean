import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_y_pxy_y_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  clear eq24
  have eq71 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k y x) := by
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
  have eq72 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq95
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq95
       grind)
    | exact superpose eq95 eq16
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq110
    | exact resolve eq110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq111
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq111
    | exact resolve eq111 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq8037 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq113 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq8037
    | exact resolve eq8037 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8037
  have eq8049 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq8038
       have r₂ := eq27
       grind)
    | exact resolve eq8038 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8038
  have eq8053 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq8049
    | exact resolve eq8049 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8049
  have eq8055 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq8053
    | exact resolve eq8053 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8053
  have eq8059 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq8055 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8055
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8055
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8055
       grind)
    | exact resolve eq13 eq8055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8055
  have eq8060 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq8059
       have r₂ := eq26
       grind)
    | exact resolve eq8059 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8059
  have eq8068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq8060 eq113
    | exact resolve eq113 eq8060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8060
  have eq8076 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8068
  have eq8078 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8076
       have r₂ := eq27
       grind)
    | exact resolve eq8076 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8076
  have eq8196 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq8078
       grind)
    | exact superpose eq8078 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq8078
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8078
       grind)
    | exact resolve eq13 eq8078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8197 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8196
       have r₂ := eq18
       grind)
    | exact resolve eq8196 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8196
  have eq8201 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq8197
       grind)
    | exact superpose eq8197 eq95
    | exact resolve eq95 eq8197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8197
  have eq8215 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8201
    | exact resolve eq8201 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8201
  have eq8362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8215 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8365 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8362
    | exact resolve eq8362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8362
  have eq8376 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8365
       have r₂ := eq27
       grind)
    | exact resolve eq8365 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8365
  have eq8380 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8376
    | exact resolve eq8376 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8376
  have eq8381 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8380
  have eq8384 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8381
    | exact resolve eq8381 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8381
  have eq8525 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8384 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8384
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8384
       grind)
    | exact resolve eq13 eq8384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8384
  have eq8526 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8525
       have r₂ := eq26
       grind)
    | exact resolve eq8525 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8525
  have eq8542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8526 eq8215
    | exact resolve eq8215 eq8526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8215 eq8526
  have eq8544 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8542
  have eq8548 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8544
       have r₂ := eq27
       grind)
    | exact resolve eq8544 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8544
  have eq8663 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8548 eq72
    | (have r₁ := eq72
       have r₂ := eq8548
       grind)
    | exact resolve eq72 eq8548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq8664 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8548 eq27
    | exact resolve eq27 eq8548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8665 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq8663
  have eq8788 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8665 eq113
    | exact resolve eq113 eq8665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8803 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq8788
  have eq8816 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8803
       have r₂ := eq8664
       grind)
    | exact resolve eq8803 eq8664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8803
  have eq8944 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8816 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq8816
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8816
       grind)
    | exact resolve eq13 eq8816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8816
  have eq8949 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8944
    | exact resolve eq8944 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8944
  have eq8952 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8949
       have r₂ := eq8078
       grind)
    | exact resolve eq8949 eq8078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8078 eq8949
  have eq9093 : (τ (σ x)) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8952 eq109
    | exact resolve eq109 eq8952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq9094 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8952 eq113
    | exact resolve eq113 eq8952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq8952
  have eq9109 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq9094
  have eq9122 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9109
       have r₂ := eq8664
       grind)
    | exact resolve eq9109 eq8664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9109
  have eq9123 : x = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq9093
    | exact resolve eq9093 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq9093
  have eq9130 : x = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq9123
       have r₂ := eq71
       grind)
    | exact resolve eq9123 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq9123
  have eq9133 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq9122
       grind)
    | exact superpose eq9122 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq9122
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9122
       grind)
    | exact resolve eq13 eq9122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9122
  have eq9134 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9133
       have r₂ := eq18
       grind)
    | exact resolve eq9133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9133
  have eq9252 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq9134
       grind)
    | exact superpose eq9134 eq95
    | exact resolve eq95 eq9134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9134
  have eq9266 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq9252
    | exact resolve eq9252 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9252
  have eq9303 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9266 eq8665
    | exact resolve eq8665 eq9266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8665
  have eq9307 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9303
  have eq9315 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9307
       have r₂ := eq8664
       grind)
    | exact resolve eq9307 eq8664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9307
  have eq9477 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9315 eq13
    | exact resolve eq13 eq9315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9315
  have eq9482 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9477
    | exact resolve eq9477 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9477
  have eq9485 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9482
       have r₂ := eq8548
       grind)
    | exact resolve eq9482 eq8548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8548 eq9482
  have eq9620 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9485 eq9266
    | exact resolve eq9266 eq9485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9266 eq9485
  have eq9623 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq9620
  have eq9635 : x = (M.op x y) := by
    first
    | (have r₁ := eq9623
       have r₂ := eq8664
       grind)
    | exact resolve eq9623 eq8664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8664 eq9623
  have eq9651 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq9635 eq20
    | exact resolve eq20 eq9635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq9754 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9651
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9651
    | exact resolve eq9651 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9651
  have eq9770 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq9754 eq26
    | exact resolve eq26 eq9754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq9954 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9635 eq9130
    | exact resolve eq9130 eq9635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9130
  have eq9958 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq9954
       grind)
    | exact superpose eq9954 eq95
    | exact resolve eq95 eq9954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9954
  have eq9981 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9754 eq9958
    | exact resolve eq9958 eq9754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9958
  have eq9989 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq9981
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9981
    | exact resolve eq9981 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9981
  have eq9996 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9754 eq9989
    | exact resolve eq9989 eq9754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9989
  have eq10010 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9996 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq9996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10011 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by grind
  clear eq10010
  have eq10013 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9770 eq10011
    | exact resolve eq10011 eq9770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10011
  have eq10024 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq10013
       have r₂ := eq27
       grind)
    | exact resolve eq10013 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10013
  have eq10035 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq9770 eq10024
    | exact resolve eq10024 eq9770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10024
  have eq10053 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq10035 eq13
    | exact resolve eq13 eq10035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10035
  have eq10054 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq10053
       have r₂ := eq9770
       grind)
    | exact resolve eq10053 eq9770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10053
  have eq10068 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq10054 eq9996
    | exact resolve eq9996 eq10054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9996 eq10054
  have eq10070 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq10068
  have eq10072 : x = (M.op y x) := by
    first
    | (have r₁ := eq10070
       have r₂ := eq27
       grind)
    | exact resolve eq10070 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10070
  have eq10094 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq10072
       grind)
    | exact superpose eq10072 eq13
    | exact resolve eq13 eq10072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10072
  have eq10099 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10094
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10094
    | exact resolve eq10094 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10094
  have eq10102 : x = (k y x) := by
    first
    | (have r₁ := eq10099
       have r₂ := eq9635
       grind)
    | exact resolve eq10099 eq9635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9635 eq10099
  have eq10109 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq10102
       grind)
    | exact superpose eq10102 eq95
    | exact resolve eq95 eq10102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq10102
  have eq10132 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq9754 eq10109
    | exact resolve eq10109 eq9754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10109
  have eq10140 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq10132
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10132
    | exact resolve eq10132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10132
  have eq10147 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq9754 eq10140
    | exact resolve eq10140 eq9754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9754 eq10140
  have eq10204 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq10147 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq10147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10205 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by grind
  clear eq10204
  have eq10207 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq9770 eq10205
    | exact resolve eq10205 eq9770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10205
  have eq10218 : (M.op (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq10207
       have r₂ := eq27
       grind)
    | exact resolve eq10207 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10207
  have eq10229 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq9770 eq10218
    | exact resolve eq10218 eq9770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10218
  have eq10289 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq10229 eq13
    | exact resolve eq13 eq10229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10229
  have eq10290 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq10289
       have r₂ := eq9770
       grind)
    | exact resolve eq10289 eq9770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9770 eq10289
  have eq10292 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10147 eq10290
    | exact resolve eq10290 eq10147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10147 eq10290
  have eq10294 : False := by grind
  exact eq10294

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyx_x_pyx_x_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = (M.op X0 X1) := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq62 (σ X0)
       grind)
    | exact superpose eq62 eq15
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq62 X0
       grind)
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq65
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1142 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq1159 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1142 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq1142
    | (have j0 := eq1142 X0 X1
       grind)
    | exact resolve eq1142 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq3843 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1159 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1159
    | exact resolve eq1159 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159
  have eq3995 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3843 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq3843
    | (have j0 := eq3843 X0 X1
       grind)
    | exact resolve eq3843 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3843
  have eq4022 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3995 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq3995 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq3995 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3995
  have eq4030 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4022 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4022
    | exact resolve eq4022 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4055 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4022 (σ X1) X0
       grind)
    | exact superpose eq4022 eq15
    | (have j1 := eq4022 (σ X1) X0
       grind)
    | exact resolve eq15 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022
  have eq4108 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq4030 (τ X0) X1
       grind)
    | exact superpose eq4030 eq18
    | (have j1 := eq4030 (τ X0) X1
       grind)
    | exact resolve eq18 eq4030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4030
  have eq4661 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4108 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4108
    | exact resolve eq4108 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108
  have eq4868 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4661 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4661
    | (have j0 := eq4661 X0 X1
       grind)
    | exact resolve eq4661 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4661
  have eq5529 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4055 x y
       grind)
    | exact superpose eq4055 eq16
    | (have j1 := eq4055 x y
       grind)
    | exact resolve eq16 eq4055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5641 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4055 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4055
  have eq5838 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5641 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq5641
    | (have j0 := eq5641 (τ X1) (τ X0)
       grind)
    | exact resolve eq5641 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq5884 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5838 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5838
    | (have j0 := eq5838 X0 X1
       grind)
    | exact resolve eq5838 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5838
  have eq5906 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5884 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5884
    | (have j0 := eq5884 X0 X1
       grind)
    | exact resolve eq5884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5884
  have eq5922 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5906 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5906
    | (have j0 := eq5906 X0 X1
       grind)
    | exact resolve eq5906 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5906
  have eq5934 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5922 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5922
    | (have j0 := eq5922 X0 X1
       grind)
    | exact resolve eq5922 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5922
  have eq6081 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5529
       have i₂ := eq4868 x y
       grind)
    | exact superpose eq4868 eq5529
    | (have j1 := eq4868 (σ x) (σ y)
       grind)
    | (have r₁ := eq5529
       have r₂ := eq4868 x y
       grind)
    | exact resolve eq5529 eq4868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4868 eq5529
  have eq6082 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6081
  have eq6085 : y ≠ y ∨ (M.op x x) = (M.op y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6082
       grind)
    | exact superpose eq6082 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6082
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6082
       grind)
    | exact resolve eq13 eq6082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6086 : (M.op x x) = (M.op y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6085
  have eq12064 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (k y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6086
       grind)
    | exact superpose eq6086 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6086
       grind)
    | exact resolve eq12 eq6086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6086
  have eq12065 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (M.op x y) = (k y x) := by grind
  clear eq12064
  have eq14245 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12065
       grind)
    | exact superpose eq12065 eq16
    | exact resolve eq16 eq12065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12065
  have eq14254 : (σ y) ≠ (σ y) ∨ y = (k y x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14245
       have i₂ := eq6082
       grind)
    | exact superpose eq6082 eq14245
    | exact resolve eq14245 eq6082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6082 eq14245
  have eq14255 : (σ y) ≠ (σ y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14254
  have eq14256 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by grind
  clear eq14255
  have eq14289 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq14256
       grind)
    | exact superpose eq14256 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq14256
       grind)
    | exact resolve eq13 eq14256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14290 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by grind
  clear eq14289
  have eq14291 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14290
       have i₂ := eq76 x
       grind)
    | exact superpose eq76 eq14290
    | exact resolve eq14290 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq14290
  have eq14295 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14291
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq14291
    | exact resolve eq14291 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14291
  have eq59972 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq90 x (σ y)
       have i₂ := eq14295
       grind)
    | exact superpose eq14295 eq90
    | (have j0 := eq90 x (σ y)
       grind)
    | (have r₁ := eq90 x (σ y)
       have r₂ := eq14295
       grind)
    | exact resolve eq90 eq14295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq14295
  have eq59993 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (k y x) := by grind
  clear eq59972
  have eq60013 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq59993
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq59993
    | exact resolve eq59993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59993
  have eq62152 : (σ y) = (σ (k y x)) ∨ y = (k y x) ∨ (σ y) = (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq14256
       have i₂ := eq60013
       grind)
    | exact superpose eq60013 eq14256
    | exact resolve eq14256 eq60013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14256 eq60013
  have eq62222 : y = (k y x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq62152
  have eq62273 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq5641 x y
       have i₂ := eq62222
       grind)
    | exact superpose eq62222 eq5641
    | (have j0 := eq5641 x y
       grind)
    | (have r₁ := eq5641 x y
       have r₂ := eq62222
       grind)
    | exact resolve eq5641 eq62222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62275 : y ≠ y ∨ y = (M.op x y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq5934 y x
       have i₂ := eq62222
       grind)
    | exact superpose eq62222 eq5934
    | (have j0 := eq5934 y x
       grind)
    | (have r₁ := eq5934 y x
       have r₂ := eq62222
       grind)
    | exact resolve eq5934 eq62222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62222
  have eq62355 : y = (M.op x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq62275
  have eq62357 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq62273
  have eq62363 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq5641 x y
       grind)
    | (have r₁ := eq62357
       have r₂ := eq5641 x y
       grind)
    | exact resolve eq62357 eq5641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5641 eq62357
  have eq62371 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62363
       grind)
    | exact superpose eq62363 eq16
    | exact resolve eq16 eq62363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62363
  have eq62384 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq62371
       have i₂ := eq62355
       grind)
    | exact superpose eq62355 eq62371
    | exact resolve eq62371 eq62355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62355
  have eq62392 : (σ y) = (σ (k y x)) := by grind
  clear eq62384
  have eq62418 : (k y x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq62392
       grind)
    | exact superpose eq62392 eq10
    | exact resolve eq10 eq62392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62392
  have eq62547 : y = (k y x) := by
    first
    | (have i₁ := eq62418
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq62418
    | exact resolve eq62418 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62418
  have eq62569 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5934 y x
       have i₂ := eq62547
       grind)
    | exact superpose eq62547 eq5934
    | (have j0 := eq5934 y x
       grind)
    | (have r₁ := eq5934 y x
       have r₂ := eq62547
       grind)
    | exact resolve eq5934 eq62547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5934 eq62547
  have eq62649 : y = (M.op x y) := by grind
  clear eq62569
  have eq62657 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq62371
       have i₂ := eq62649
       grind)
    | exact superpose eq62649 eq62371
    | exact resolve eq62371 eq62649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62371 eq62649
  have eq62665 : False := by grind
  exact eq62665

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
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
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
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
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq52 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq47 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq47 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq54 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq48 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq48 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq49 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq49 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq49 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq52 X1 X0
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq54 X1 X0
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq54
  have eq67 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq21 X1
       grind)
    | exact superpose eq21 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq56
  have eq124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq128 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       have j1 := eq67 X1 X0
       grind)
    | (have r₁ := eq124 X1 X0
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq124 X1 X1
       have r₂ := eq67 X1 X1
       grind)
    | exact resolve eq124 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq124
  have eq326 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq128 (σ X1) (σ X0)
       grind)
    | exact superpose eq128 eq15
    | exact resolve eq15 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq326 X0 X1
       have i₂ := eq128 X1 X0
       grind)
    | exact superpose eq128 eq326
    | exact resolve eq326 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq326
  have eq336 : False := by grind
  exact eq336

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq273 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq275 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq276 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq277 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq274 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq274 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq274 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq294 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq277 (τ X0)
       grind)
    | exact superpose eq277 eq31
    | exact resolve eq31 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq294 X0
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq294
    | exact resolve eq294 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq382 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq276 X0 X1
       grind)
    | exact superpose eq276 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq276 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq276 X0 X1
       grind)
    | exact resolve eq13 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq276 (σ x) (σ y)
       grind)
    | exact superpose eq276 eq16
    | (have j1 := eq276 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq389 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq385
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq385
    | exact resolve eq385 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq390 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq388 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq388 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq388 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq403 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq390 X0 (σ X1)
       grind)
    | exact superpose eq390 eq22
    | (have j1 := eq390 X0 (σ X1)
       grind)
    | exact resolve eq22 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq421 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq421
    | (have j0 := eq421 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       grind)
    | (have r₁ := eq421 X0 (M.op (M.op X1 X1) (M.op X0 X0))
       have r₂ := eq9 X0 X1
       grind)
    | exact resolve eq421 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq434 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq456 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) (M.op (τ X0) (τ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 X1) (M.op (τ X0) (τ X0)))
       have i₂ := eq434 (τ X0) X1
       grind)
    | exact superpose eq434 eq17
    | exact resolve eq17 eq434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq461 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 X1) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq456 X0 X1
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq456
    | exact resolve eq456 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq467 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op X1 X1) (τ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq461 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq461
    | exact resolve eq461 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq2308 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq403 (σ X0) X1
       grind)
    | exact superpose eq403 eq28
    | (have j1 := eq403 (σ X0) X1
       grind)
    | exact resolve eq28 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq403
  have eq2319 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2308 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2308
    | (have j0 := eq2308 X0 X1
       grind)
    | exact resolve eq2308 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308
  have eq2333 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2319 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2319
    | (have j0 := eq2319 X0 X1
       grind)
    | exact resolve eq2319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2342 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2333 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2333
    | (have j0 := eq2333 X0 X1
       grind)
    | exact resolve eq2333 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2333
  have eq2396 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k X1 (τ X0)) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2342 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2342
    | (have j0 := eq2342 X1 (τ X0)
       grind)
    | exact resolve eq2342 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2433 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq2342 X0 X1
       grind)
    | exact superpose eq2342 eq11
    | (have j1 := eq2342 X0 X1
       grind)
    | exact resolve eq11 eq2342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq2491 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2433 X0 X1
       have i₂ := eq390 X0 X1
       grind)
    | exact superpose eq390 eq2433
    | (have j0 := eq2433 X0 X1
       have j1 := eq390 X0 X1
       grind)
    | exact resolve eq2433 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2495 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2433 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq2433
    | exact resolve eq2433 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433
  have eq2537 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2495 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2495
    | (have j0 := eq2495 X0 X1
       grind)
    | exact resolve eq2495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2495
  have eq2538 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2491 X0 X1
       have j1 := eq421 X0 X1
       grind)
    | (have r₁ := eq2491 X0 X1
       have r₂ := eq421 X0 X1
       grind)
    | exact resolve eq2491 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq2491
  have eq2542 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2537 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2537
    | (have j0 := eq2537 X0 X1
       grind)
    | exact resolve eq2537 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2537
  have eq2545 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2542 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2542
    | (have j0 := eq2542 X0 X1
       grind)
    | exact resolve eq2542 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542
  have eq2571 : ∀ X0 X1 X2 : G, (k (τ X0) (τ X2)) = (τ (k (k X0 X1) X2)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (k X0 X1)
       have i₂ := eq2545 X0 X1
       grind)
    | exact superpose eq2545 eq31
    | (have j1 := eq2545 X0 X1
       grind)
    | exact resolve eq31 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2572 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op (k X0 X1) (k X0 X1))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq301 (k X0 X1)
       have i₂ := eq2545 X0 X1
       grind)
    | exact superpose eq2545 eq301
    | (have j1 := eq2545 X0 X1
       grind)
    | exact resolve eq301 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545
  have eq2580 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op (k X0 X1) (k X0 X1))) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2572 X0 X1
       have i₂ := eq301 X0
       grind)
    | exact superpose eq301 eq2572
    | (have j0 := eq2572 X0 X1
       grind)
    | exact resolve eq2572 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2572
  have eq2581 : ∀ X0 X1 X2 : G, (τ (k X0 X2)) = (τ (k (k X0 X1) X2)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2571 X0 X1 X2
       have i₂ := eq31 X2 X0
       grind)
    | exact superpose eq31 eq2571
    | (have j0 := eq2571 X0 X1 X2
       grind)
    | exact resolve eq2571 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq2627 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (σ (M.op (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq2538 (τ X0) X1
       grind)
    | exact superpose eq2538 eq17
    | (have j1 := eq2538 (τ X0) X1
       grind)
    | exact resolve eq17 eq2538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq2636 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op (σ (τ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2627 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2627
    | (have j0 := eq2627 X0 X1
       grind)
    | exact resolve eq2627 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2627
  have eq2645 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2636 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2636
    | (have j0 := eq2636 X0 X1
       grind)
    | exact resolve eq2636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2636
  have eq3317 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2396 X0 (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq2396
    | exact resolve eq2396 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2396
  have eq3339 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3317 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3317
    | (have j0 := eq3317 X0 X1
       grind)
    | exact resolve eq3317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3317
  have eq3538 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3339 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3339
  have eq4453 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2645 (σ X0) X1
       grind)
    | exact superpose eq2645 eq15
    | (have j1 := eq2645 (σ X0) X1
       grind)
    | exact resolve eq15 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2645
  have eq4474 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4453 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4453
    | (have j0 := eq4453 X0 X1
       grind)
    | exact resolve eq4453 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453
  have eq13873 : ∀ X0 X1 X2 : G, (τ (k X0 (σ X1))) = (k (τ (k X0 X2)) X1) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (k X0 X2) X1
       have i₂ := eq2581 X0 X2 (σ X1)
       grind)
    | exact superpose eq2581 eq22
    | (have j1 := eq2581 X0 X2 X2
       grind)
    | exact resolve eq22 eq2581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13878 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (k X0 X2) X1) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (k X0 X2) X1)
       have i₂ := eq2581 X0 X2 X1
       grind)
    | exact superpose eq2581 eq11
    | (have j1 := eq2581 X0 X2 X2
       grind)
    | exact resolve eq11 eq2581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2581
  have eq13934 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k X0 X1) = (k (k X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13878 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq13878
    | (have j0 := eq13878 X0 X1 X2
       grind)
    | exact resolve eq13878 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13878
  have eq13937 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X0 X2) ∨ (k (τ X0) X1) = (k (τ (k X0 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13873 X0 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq13873
    | (have j0 := eq13873 X0 X1 X2
       grind)
    | exact resolve eq13873 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13873
  have eq14004 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k (k X0 X1) X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4474 X0 X1
       have i₂ := eq13934 X0 X2 X1
       grind)
    | exact superpose eq13934 eq4474
    | (have j0 := eq4474 X0 X1
       have j1 := eq13934 X0 X2 X1
       grind)
    | exact resolve eq4474 eq13934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13934
  have eq18890 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (τ (σ X0)) X2) = (k (τ (k (σ X0) (σ X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq13937 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq13937 eq15
    | (have j1 := eq13937 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq15 eq13937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13937
  have eq18958 : ∀ X0 X1 X2 : G, (k (k (τ (σ X0)) X1) X2) = (k (τ (σ X0)) X2) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18890 X0 X1 X2
       have i₂ := eq22 (σ X0) X1
       grind)
    | exact superpose eq22 eq18890
    | (have j0 := eq18890 X0 X1 X2
       grind)
    | exact resolve eq18890 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18890
  have eq19022 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k (k X0 X1) X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18958 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18958
    | (have j0 := eq18958 X0 X1 X2
       grind)
    | exact resolve eq18958 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18958
  have eq45982 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (k (k x y) X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq19022 x y X0
       grind)
    | exact superpose eq19022 eq16
    | (have j1 := eq19022 x y X0
       grind)
    | exact resolve eq16 eq19022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19022
  have eq46952 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k (k x y) X0) = (k x X0) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq45982 X0
       have i₂ := eq4474 x y
       grind)
    | exact superpose eq4474 eq45982
    | (have j0 := eq45982 X0
       have j1 := eq4474 x y
       grind)
    | exact resolve eq45982 eq4474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4474 eq45982
  have eq46966 : ∀ X0 : G, (k (k x y) X0) = (k x X0) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq46952 X0
       have j1 := eq14004 x y X0
       grind)
    | (have r₁ := eq46952 X0
       have r₂ := eq14004 x y x
       grind)
    | exact resolve eq46952 eq14004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14004 eq46952
  have eq46968 : ∀ X0 : G, (k (k x y) X0) = (k x X0) := by
    intro X0
    first
    | (have j0 := eq46966 X0
       grind)
    | (have r₁ := eq46966 X0
       have r₂ := eq16
       grind)
    | exact resolve eq46966 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46966
  have eq47094 : (M.op (k x y) (k x y)) = (k x (k x y)) := by
    first
    | (have i₁ := eq277 (k x y)
       have i₂ := eq46968 (k x y)
       grind)
    | exact superpose eq46968 eq277
    | exact resolve eq277 eq46968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq47095 : ∀ X0 : G, (k x X0) = (M.op (k x y) X0) ∨ (k x y) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq390 (k x y) X0
       have i₂ := eq46968 X0
       grind)
    | exact superpose eq46968 eq390
    | exact resolve eq390 eq46968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49368 : ∀ X0 : G, (k X0 (σ (M.op (k x (k x y)) (τ (M.op X0 X0))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq467 X0 (k x y)
       have i₂ := eq47094
       grind)
    | exact superpose eq47094 eq467
    | exact resolve eq467 eq47094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq53905 : (k x y) = (k x (σ (M.op (k x (k x y)) (τ (M.op (k x y) (k x y)))))) := by
    first
    | (have i₁ := eq46968 (σ (M.op (k x (k x y)) (τ (M.op (k x y) (k x y)))))
       have i₂ := eq49368 (k x y)
       grind)
    | exact superpose eq49368 eq46968
    | exact resolve eq46968 eq49368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46968
  have eq53913 : (k x y) = (k x (σ (M.op (k x (k x y)) (τ (k x (k x y)))))) := by
    first
    | (have i₁ := eq53905
       have i₂ := eq47094
       grind)
    | exact superpose eq47094 eq53905
    | exact resolve eq53905 eq47094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53905
  have eq58352 : ∀ X0 : G, x = (k x y) ∨ (M.op x y) = (k x X0) ∨ (k x X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq47095 X0
       have i₂ := eq390 x y
       grind)
    | exact superpose eq390 eq47095
    | (have j1 := eq390 x y
       grind)
    | exact resolve eq47095 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq47095
  have eq240263 : (M.op x y) = (k x y) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq2580 x y
       have i₂ := eq47094
       grind)
    | exact superpose eq47094 eq2580
    | (have j0 := eq2580 x y
       grind)
    | exact resolve eq2580 eq47094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580
  have eq241212 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq2538 x y
       have i₂ := eq240263
       grind)
    | exact superpose eq240263 eq2538
    | (have j0 := eq2538 x y
       grind)
    | exact resolve eq2538 eq240263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2538 eq240263
  have eq241242 : x = (M.op x y) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have r₁ := eq241212
       have r₂ := eq16
       grind)
    | exact resolve eq241212 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241212
  have eq241259 : (τ x) ≠ (τ x) ∨ (τ x) = (τ (k x y)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq3538 x y
       have i₂ := eq241242
       grind)
    | exact superpose eq241242 eq3538
    | (have j0 := eq3538 x y
       grind)
    | exact resolve eq3538 eq241242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538 eq241242
  have eq241262 : (τ x) = (τ (k x y)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by grind
  clear eq241259
  have eq243123 : (τ (M.op (k x y) (k x y))) = (M.op (τ x) (τ x)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq301 (k x y)
       have i₂ := eq241262
       grind)
    | exact superpose eq241262 eq301
    | exact resolve eq301 eq241262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241262
  have eq243410 : (τ (M.op (k x y) (k x y))) = (τ (M.op x x)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq243123
       have i₂ := eq301 x
       grind)
    | exact superpose eq301 eq243123
    | exact resolve eq243123 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301 eq243123
  have eq243524 : (τ (k x (k x y))) = (τ (M.op x x)) ∨ (τ (k x (k x y))) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq243410
       have i₂ := eq47094
       grind)
    | exact superpose eq47094 eq243410
    | exact resolve eq243410 eq47094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47094 eq243410
  have eq243525 : (τ (k x (k x y))) = (τ (M.op x x)) := by grind
  clear eq243524
  have eq243641 : (k x y) = (k x (σ (M.op (k x (k x y)) (τ (M.op x x))))) := by
    first
    | (have i₁ := eq53913
       have i₂ := eq243525
       grind)
    | exact superpose eq243525 eq53913
    | exact resolve eq53913 eq243525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53913 eq243525
  have eq243975 : x = (k x y) := by
    first
    | (have i₁ := eq243641
       have i₂ := eq49368 x
       grind)
    | exact superpose eq49368 eq243641
    | exact resolve eq243641 eq49368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49368 eq243641
  have eq1781313 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (k x y) = (M.op (M.op x y) y) := by
    first
    | (have j0 := eq58352 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58352
  have eq1781314 : (M.op x y) = (k x y) ∨ (k x y) = (M.op (M.op x y) y) := by
    first
    | (have j1 := eq276 x y
       grind)
    | (have r₁ := eq1781313
       have r₂ := eq276 x y
       grind)
    | exact resolve eq1781313 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781313
  have eq1781575 : x = (M.op x y) ∨ (k x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1781314
       have i₂ := eq243975
       grind)
    | exact superpose eq243975 eq1781314
    | exact resolve eq1781314 eq243975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781314
  have eq1781576 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1781575
       have i₂ := eq243975
       grind)
    | exact superpose eq243975 eq1781575
    | exact resolve eq1781575 eq243975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781575
  have eq1781578 : x = (M.op x y) ∨ x = (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1781576
       have i₂ := eq276 (M.op x y) y
       grind)
    | exact superpose eq276 eq1781576
    | (have j1 := eq276 x y
       grind)
    | exact resolve eq1781576 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781576
  have eq1781591 : x = (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by grind
  clear eq1781578
  have eq1782020 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq389
       have i₂ := eq1781591
       grind)
    | exact superpose eq1781591 eq389
    | exact resolve eq389 eq1781591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781591
  have eq1782061 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by grind
  clear eq1782020
  have eq1782062 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1782061
       have i₂ := eq243975
       grind)
    | exact superpose eq243975 eq1782061
    | exact resolve eq1782061 eq243975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782061
  have eq1782094 : (σ (M.op x y)) ≠ (σ x) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1782062
       grind)
    | exact superpose eq1782062 eq16
    | exact resolve eq16 eq1782062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782062
  have eq1782444 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1782094
       have i₂ := eq276 x y
       grind)
    | exact superpose eq276 eq1782094
    | (have j1 := eq276 x y
       grind)
    | exact resolve eq1782094 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq1782094
  have eq1782448 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by grind
  clear eq1782444
  have eq1782449 : (M.op x y) = (k x y) := by grind
  clear eq1782448
  have eq1782453 : x = (M.op x y) := by
    first
    | (have i₁ := eq1782449
       have i₂ := eq243975
       grind)
    | exact superpose eq243975 eq1782449
    | exact resolve eq1782449 eq243975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782449
  have eq1782457 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq389
       have i₂ := eq1782453
       grind)
    | exact superpose eq1782453 eq389
    | exact resolve eq389 eq1782453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq1782500 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq1782457
  have eq1782502 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1782500
       have i₂ := eq243975
       grind)
    | exact superpose eq243975 eq1782500
    | exact resolve eq1782500 eq243975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243975 eq1782500
  have eq1782535 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1782502
       grind)
    | exact superpose eq1782502 eq16
    | exact resolve eq16 eq1782502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782502
  have eq1782816 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1782535
       have i₂ := eq1782453
       grind)
    | exact superpose eq1782453 eq1782535
    | exact resolve eq1782535 eq1782453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782453 eq1782535
  have eq1782817 : False := by grind
  exact eq1782817

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq461 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq461 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq461 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq461 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461
  have eq473 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq462 (σ X0)
       grind)
    | exact superpose eq462 eq15
    | exact resolve eq15 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq462 (τ X0)
       grind)
    | exact superpose eq462 eq31
    | exact resolve eq31 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq486 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq479 X0
       have i₂ := eq462 X0
       grind)
    | exact superpose eq462 eq479
    | exact resolve eq479 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq492 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq473 X0
       have i₂ := eq462 X0
       grind)
    | exact superpose eq462 eq473
    | exact resolve eq473 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462 eq473
  have eq739 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq781 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq739 X0 X1
       have i₂ := eq492 X0
       grind)
    | exact superpose eq492 eq739
    | (have j0 := eq739 X0 X1
       grind)
    | exact resolve eq739 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq3159 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq781 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq781
    | exact resolve eq781 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq3344 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3159 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq3159
    | (have j0 := eq3159 X0 X1
       grind)
    | exact resolve eq3159 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3159
  have eq3352 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3344 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq3344 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq3344 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3344
  have eq3354 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3352 X0 X1
       have i₂ := eq486 X0
       grind)
    | exact superpose eq486 eq3352
    | (have j0 := eq3352 X0 X1
       grind)
    | exact resolve eq3352 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq3352
  have eq3355 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3354 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3354
    | (have j0 := eq3354 X0 X1
       grind)
    | exact resolve eq3354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq3356 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3355 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3355
    | exact resolve eq3355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3376 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3355 (σ X0) X1
       grind)
    | exact superpose eq3355 eq15
    | (have j1 := eq3355 (σ X0) X1
       grind)
    | exact resolve eq15 eq3355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq3418 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3376 X0 X1
       have i₂ := eq492 X0
       grind)
    | exact superpose eq492 eq3376
    | (have j0 := eq3376 X0 X1
       grind)
    | exact resolve eq3376 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq3547 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq3356 (τ X1) X0
       grind)
    | exact superpose eq3356 eq17
    | (have j1 := eq3356 (τ X1) X0
       grind)
    | exact resolve eq17 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3356
  have eq5428 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3547 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3547
    | exact resolve eq3547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq5529 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5428 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5428
    | (have j0 := eq5428 X0 X1
       grind)
    | exact resolve eq5428 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5428
  have eq22449 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3418 x y
       grind)
    | exact superpose eq3418 eq16
    | (have j1 := eq3418 x y
       grind)
    | exact resolve eq16 eq3418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22817 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3418 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3418
  have eq22939 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq22449
       have i₂ := eq5529 y x
       grind)
    | exact superpose eq5529 eq22449
    | (have j1 := eq5529 y x
       grind)
    | (have r₁ := eq22449
       have r₂ := eq5529 y x
       grind)
    | exact resolve eq22449 eq5529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22449
  have eq22940 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq22939
  have eq22943 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq22940
       grind)
    | exact superpose eq22940 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22940
       grind)
    | exact resolve eq13 eq22940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22944 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq22940
       grind)
    | exact superpose eq22940 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq22940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22940
  have eq22945 : x = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq22943
  have eq22946 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq22945
       have r₂ := eq22944
       grind)
    | exact resolve eq22945 eq22944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22944 eq22945
  have eq23105 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22817 x y
       have i₂ := eq22946
       grind)
    | exact superpose eq22946 eq22817
    | (have j0 := eq22817 x y
       grind)
    | exact resolve eq22817 eq22946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22817 eq22946
  have eq23129 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq23105
  have eq23130 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq23129
  have eq23522 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23130
       grind)
    | exact superpose eq23130 eq16
    | exact resolve eq16 eq23130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23524 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq23130
       grind)
    | exact superpose eq23130 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq23130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23525 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq23130
       grind)
    | exact superpose eq23130 eq12
    | exact resolve eq12 eq23130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23130
  have eq23526 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq23525
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq23525
    | exact resolve eq23525 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23525
  have eq23527 : (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq23524
       have r₂ := eq492 x
       grind)
    | exact resolve eq23524 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23524
  have eq23528 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq23527
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq23527
    | exact resolve eq23527 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23527
  have eq23529 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq23528
       have i₂ := eq492 x
       grind)
    | exact superpose eq492 eq23528
    | exact resolve eq23528 eq492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492 eq23528
  have eq23530 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq23529
       have r₂ := eq23526
       grind)
    | exact resolve eq23529 eq23526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23526 eq23529
  have eq23539 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5529 y x
       have i₂ := eq23530
       grind)
    | exact superpose eq23530 eq5529
    | (have j0 := eq5529 y x
       grind)
    | exact resolve eq5529 eq23530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5529 eq23530
  have eq23634 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq23539
       have r₂ := eq23522
       grind)
    | exact resolve eq23539 eq23522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23539
  have eq23656 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq23522
       have i₂ := eq23634
       grind)
    | exact superpose eq23634 eq23522
    | exact resolve eq23522 eq23634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23522 eq23634
  have eq23660 : False := by grind
  exact eq23660

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  clear eq18
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
  have eq318 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq318
  have eq326 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq320 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq339 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq326 (σ X0)
       grind)
    | exact superpose eq326 eq15
    | exact resolve eq15 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq326 (τ X0)
       grind)
    | exact superpose eq326 eq32
    | exact resolve eq32 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq345 X0
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq345
    | exact resolve eq345 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq358 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq339 X0
       have i₂ := eq326 X0
       grind)
    | exact superpose eq326 eq339
    | exact resolve eq339 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326 eq339
  have eq404 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (σ X0) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq358 X0
       grind)
    | exact superpose eq358 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq411 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq405 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq405
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq416 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq411
  have eq613 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq616 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq641 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1
       have i₂ := eq358 X0
       grind)
    | exact superpose eq358 eq616
    | (have j0 := eq616 X0 X1
       grind)
    | exact resolve eq616 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq642 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq613 X0 X1
       have i₂ := eq352 X1
       grind)
    | exact superpose eq352 eq613
    | (have j0 := eq613 X0 X1
       grind)
    | exact resolve eq613 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq655 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq641 X0 X1
       have i₂ := eq358 X1
       grind)
    | exact superpose eq358 eq641
    | (have j0 := eq641 X0 X1
       grind)
    | exact resolve eq641 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq4226 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq655 x y
       grind)
    | exact superpose eq655 eq16
    | (have j1 := eq655 x y
       grind)
    | exact resolve eq16 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4339 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq655 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq10740 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq642 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq642
    | (have j0 := eq642 X1 (σ X0)
       grind)
    | exact resolve eq642 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq10854 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10740 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10740
    | (have j0 := eq10740 X0 X1
       grind)
    | exact resolve eq10740 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10740
  have eq10875 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10854 X0 X1
       have i₂ := eq358 X0
       grind)
    | exact superpose eq358 eq10854
    | (have j0 := eq10854 X0 X1
       grind)
    | exact resolve eq10854 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10854
  have eq10887 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10875 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq10875
    | (have j0 := eq10875 X0 X1
       grind)
    | exact resolve eq10875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10875
  have eq22970 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4226
       have i₂ := eq10887 y x
       grind)
    | exact superpose eq10887 eq4226
    | (have j1 := eq10887 y x
       grind)
    | (have r₁ := eq4226
       have r₂ := eq10887 y x
       grind)
    | exact resolve eq4226 eq10887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4226 eq10887
  have eq22971 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq22970
  have eq29945 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4339 (τ X0) (τ X1)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq4339
    | (have j0 := eq4339 (τ X0) (τ X1)
       grind)
    | exact resolve eq4339 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq30026 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29945 X0 X1
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq29945
    | (have j0 := eq29945 X0 X1
       grind)
    | exact resolve eq29945 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29945
  have eq30073 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30026 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq30026
    | (have j0 := eq30026 X0 X1
       grind)
    | exact resolve eq30026 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30026
  have eq30114 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30073 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq30073
    | (have j0 := eq30073 X0 X1
       grind)
    | exact resolve eq30073 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30073
  have eq30144 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30114 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq30114
    | (have j0 := eq30114 X0 X1
       grind)
    | exact resolve eq30114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30114
  have eq30168 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30144 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30144
    | (have j0 := eq30144 X0 X1
       grind)
    | exact resolve eq30144 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30144
  have eq30190 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30168 X0 X1
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq30168
    | (have j0 := eq30168 X0 X1
       grind)
    | exact resolve eq30168 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30168
  have eq30206 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30190 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq30190
    | (have j0 := eq30190 X0 X1
       grind)
    | exact resolve eq30190 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30190
  have eq30221 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30206 X0 X1
       have i₂ := eq352 X1
       grind)
    | exact superpose eq352 eq30206
    | (have j0 := eq30206 X0 X1
       grind)
    | exact resolve eq30206 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq30206
  have eq30232 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ X0)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq30221 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq30221
    | (have j0 := eq30221 X0 X1
       grind)
    | exact resolve eq30221 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30221
  have eq30243 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30232 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30232
    | (have j0 := eq30232 X0 X1
       grind)
    | exact resolve eq30232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30232
  have eq92907 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq22971
       grind)
    | exact superpose eq22971 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22971
       grind)
    | exact resolve eq13 eq22971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22971
  have eq92908 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq92907
  have eq92909 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq92908
  have eq111602 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq404 x (σ y)
       have i₂ := eq92909
       grind)
    | exact superpose eq92909 eq404
    | (have j0 := eq404 x (σ y)
       grind)
    | (have r₁ := eq404 x (σ y)
       have r₂ := eq92909
       grind)
    | exact resolve eq404 eq92909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92909
  have eq111622 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq111602
  have eq111625 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111622
       have i₂ := eq358 y
       grind)
    | exact superpose eq358 eq111622
    | exact resolve eq111622 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111622
  have eq111626 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq111625
  have eq111630 : (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111626
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq111626
    | exact resolve eq111626 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111626
  have eq111639 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4339 x y
       have i₂ := eq111630
       grind)
    | exact superpose eq111630 eq4339
    | (have j0 := eq4339 x y
       grind)
    | (have r₁ := eq4339 x y
       have r₂ := eq111630
       grind)
    | exact resolve eq4339 eq111630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111630
  have eq111747 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ x = (M.op y y) := by grind
  clear eq111639
  have eq111748 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ x = (M.op y y) := by grind
  clear eq111747
  have eq111752 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq4339 x y
       grind)
    | (have r₁ := eq111748
       have r₂ := eq4339 x y
       grind)
    | exact resolve eq111748 eq4339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4339 eq111748
  have eq111755 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq111752
       grind)
    | exact superpose eq111752 eq16
    | exact resolve eq16 eq111752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111756 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq404 x (σ y)
       have i₂ := eq111752
       grind)
    | exact superpose eq111752 eq404
    | (have j0 := eq404 x (σ y)
       grind)
    | (have r₁ := eq404 x (σ y)
       have r₂ := eq111752
       grind)
    | exact resolve eq404 eq111752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq111752
  have eq111776 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq111756
  have eq111779 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111776
       have i₂ := eq358 y
       grind)
    | exact superpose eq358 eq111776
    | exact resolve eq111776 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq111776
  have eq111780 : (σ x) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq111779
  have eq111784 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111780
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq111780
    | exact resolve eq111780 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111780
  have eq111801 : (k x y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq111784
       grind)
    | exact superpose eq111784 eq10
    | exact resolve eq10 eq111784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111784
  have eq112110 : (k x y) = (M.op x x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq111801
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq111801
    | exact resolve eq111801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111801
  have eq112160 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq30243 x y
       have i₂ := eq112110
       grind)
    | exact superpose eq112110 eq30243
    | (have j0 := eq30243 x y
       grind)
    | (have r₁ := eq30243 x y
       have r₂ := eq112110
       grind)
    | exact resolve eq30243 eq112110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30243 eq112110
  have eq112189 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq112160
  have eq112190 : (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq112189
  have eq112234 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq111755
       have i₂ := eq112190
       grind)
    | exact superpose eq112190 eq111755
    | exact resolve eq111755 eq112190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111755 eq112190
  have eq112241 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq112234
  have eq112242 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq112241
  have eq112433 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq112242
       grind)
    | exact superpose eq112242 eq10
    | exact resolve eq10 eq112242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112242
  have eq112735 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq112433
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq112433
    | exact resolve eq112433 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112433
  have eq112736 : x = (M.op y y) := by grind
  clear eq112735
  have eq112759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq416 y
       have i₂ := eq112736
       grind)
    | exact superpose eq112736 eq416
    | exact resolve eq416 eq112736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq112736
  have eq113191 : False := by grind
  exact eq113191

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq38 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq198 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq16
    | (have j1 := eq85 x y
       grind)
    | exact resolve eq16 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq1207 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq204 (τ X1) (τ X0)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq204
    | (have j0 := eq204 (τ X1) (τ X0)
       grind)
    | exact resolve eq204 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1226 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1207 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1207
    | (have j0 := eq1207 X0 X1
       grind)
    | exact resolve eq1207 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq1234 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1226 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1226
    | (have j0 := eq1226 X0 X1
       grind)
    | exact resolve eq1226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1241 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1234 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1234
    | (have j0 := eq1234 X0 X1
       grind)
    | exact resolve eq1234 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1247 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1241 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1241
    | (have j0 := eq1241 X0 X1
       grind)
    | exact resolve eq1241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1251 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ X0)) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1247 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1247
    | (have j0 := eq1247 X0 X1
       grind)
    | exact resolve eq1247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1253 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1251 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1251
    | (have j0 := eq1251 X0 X1
       grind)
    | exact resolve eq1251 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq2954 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq84 X1 X0
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq84 X1 X0
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq84 X0 (σ X0)
       grind)
    | (have r₁ := eq13 (M.op (σ X0) (σ X0)) X1
       have r₂ := eq84 X0 (M.op X1 (M.op (σ X0) (σ X0)))
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2959 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 X0 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq2960 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2959 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2959
  have eq2961 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2954 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954
  have eq2962 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op (σ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2961 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2961
  have eq2966 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2960 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2960
    | (have j0 := eq2960 X0
       grind)
    | exact resolve eq2960 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2960
  have eq3022 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq2966 X0
       grind)
    | exact superpose eq2966 eq38
    | (have j1 := eq2966 X0
       grind)
    | exact resolve eq38 eq2966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2966
  have eq3040 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3022 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3022
    | (have j0 := eq3022 X0
       grind)
    | exact resolve eq3022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022
  have eq3041 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3040 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3040
  have eq3044 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3041 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3041
    | exact resolve eq3041 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3066 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq3041 X0
       grind)
    | exact superpose eq3041 eq11
    | exact resolve eq11 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3107 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3044 X0
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq3044
    | exact resolve eq3044 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044
  have eq3212 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3107 X0
       grind)
    | exact superpose eq3107 eq11
    | exact resolve eq11 eq3107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3285 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq3212 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3212
    | exact resolve eq3212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212
  have eq3346 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq3285 (τ X0)
       grind)
    | exact superpose eq3285 eq34
    | exact resolve eq34 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3391 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3346 X0
       have i₂ := eq3107 X0
       grind)
    | exact superpose eq3107 eq3346
    | exact resolve eq3346 eq3107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107 eq3346
  have eq3871 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq3896 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3871 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq3871
    | exact resolve eq3871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871
  have eq3936 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3896 X0
       have i₂ := eq3285 X0
       grind)
    | exact superpose eq3285 eq3896
    | exact resolve eq3896 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq3957 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq3936
  have eq83544 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2962 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2962
    | exact resolve eq2962 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83690 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X0 (σ X1)
       have i₂ := eq2962 (σ X0) X1
       grind)
    | exact superpose eq2962 eq30
    | (have j1 := eq2962 (σ X0) X1
       grind)
    | exact resolve eq30 eq2962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2962
  have eq83837 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq83690 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq83690
    | (have j0 := eq83690 X0 X1
       grind)
    | exact resolve eq83690 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83690
  have eq83937 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83544 X0 X1
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq83544
    | (have j0 := eq83544 X0 X1
       grind)
    | exact resolve eq83544 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83544
  have eq83991 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq83837 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83837
    | (have j0 := eq83837 X0 X1
       grind)
    | exact resolve eq83837 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83837
  have eq84133 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq83991 X0 X1
       have i₂ := eq3066 X1
       grind)
    | exact superpose eq3066 eq83991
    | (have j0 := eq83991 X0 X1
       grind)
    | exact resolve eq83991 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83991
  have eq84251 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq84133 X0 X1
       have i₂ := eq3285 X1
       grind)
    | exact superpose eq3285 eq84133
    | (have j0 := eq84133 X0 X1
       grind)
    | exact resolve eq84133 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84133
  have eq84336 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq84251 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84251
    | (have j0 := eq84251 X0 X1
       grind)
    | exact resolve eq84251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84251
  have eq84767 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq83937 X0 X1
       grind)
    | exact superpose eq83937 eq11
    | (have j1 := eq83937 X0 X1
       grind)
    | exact resolve eq11 eq83937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83937
  have eq85039 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84767 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq84767
    | (have j0 := eq84767 X0 X1
       grind)
    | exact resolve eq84767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84767
  have eq85426 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq85039 (τ X0) X1
       grind)
    | exact superpose eq85039 eq19
    | (have j1 := eq85039 (τ X0) X1
       grind)
    | exact resolve eq19 eq85039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq85039
  have eq85737 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85426 X0 X1
       have i₂ := eq3391 X0
       grind)
    | exact superpose eq3391 eq85426
    | (have j0 := eq85426 X0 X1
       grind)
    | exact resolve eq85426 eq3391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85426
  have eq87161 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq84336 (τ X1) (τ X0)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq84336
    | (have j0 := eq84336 (τ X0) (τ X1)
       grind)
    | exact resolve eq84336 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq84336
  have eq87666 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq87161 X0 X1
       have i₂ := eq3391 X1
       grind)
    | exact superpose eq3391 eq87161
    | (have j0 := eq87161 X0 X1
       grind)
    | exact resolve eq87161 eq3391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391 eq87161
  have eq87865 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq87666 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq87666
    | (have j0 := eq87666 X0 X1
       grind)
    | exact resolve eq87666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87666
  have eq88038 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq87865 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87865
    | (have j0 := eq87865 X0 X1
       grind)
    | exact resolve eq87865 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87865
  have eq88169 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88038 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88038
    | (have j0 := eq88038 X0 X1
       grind)
    | exact resolve eq88038 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88038
  have eq88260 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88169 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq88169
    | (have j0 := eq88169 X0 X1
       grind)
    | exact resolve eq88169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88169
  have eq88767 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq88260 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88260
  have eq94407 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq85737 X1 (τ X0)
       grind)
    | exact superpose eq85737 eq18
    | (have j1 := eq85737 X1 (τ X0)
       grind)
    | exact resolve eq18 eq85737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq85737
  have eq94524 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94407 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq94407
    | (have j0 := eq94407 X0 X1
       grind)
    | exact resolve eq94407 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94407
  have eq94656 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94524 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94524
    | (have j0 := eq94524 X0 X1
       grind)
    | exact resolve eq94524 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94524
  have eq94771 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X0 ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq94656 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94656
    | (have j0 := eq94656 X0 X1
       grind)
    | exact resolve eq94656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94656
  have eq104603 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 ∨ (τ X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq94771 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94771
    | (have j0 := eq94771 X1 (σ X0)
       grind)
    | exact resolve eq94771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94771
  have eq105094 : ∀ X0 X1 : G, (τ X1) = (k X0 X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104603 X0 X1
       have i₂ := eq3041 X0
       grind)
    | exact superpose eq3041 eq104603
    | (have j0 := eq104603 X0 X1
       grind)
    | exact resolve eq104603 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041 eq104603
  have eq105196 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq105094 X0 X1
       have i₂ := eq3285 X0
       grind)
    | exact superpose eq3285 eq105094
    | (have j0 := eq105094 X0 X1
       grind)
    | exact resolve eq105094 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105094
  have eq112474 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 (τ (σ X0)))) ∨ (M.op X1 X1) = (τ (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105196 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq105196
    | (have j0 := eq105196 X1 (σ X0)
       grind)
    | exact resolve eq105196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105196
  have eq112796 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X1) = (τ (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq112474 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112474
    | (have j0 := eq112474 X0 X1
       grind)
    | exact resolve eq112474 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112474
  have eq112953 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq112796 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq112796
    | (have j0 := eq112796 X0 X1
       grind)
    | exact resolve eq112796 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112796
  have eq114628 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq198
       have i₂ := eq112953 y x
       grind)
    | exact superpose eq112953 eq198
    | (have j1 := eq112953 y x
       grind)
    | (have r₁ := eq198
       have r₂ := eq112953 y x
       grind)
    | exact resolve eq198 eq112953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq112953
  have eq114792 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq114628
  have eq114878 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq204 x y
       grind)
    | (have r₁ := eq114792
       have r₂ := eq204 x y
       grind)
    | exact resolve eq114792 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq114792
  have eq115040 : (σ y) = (σ (k x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq114878
       have i₂ := eq3066 x
       grind)
    | exact superpose eq3066 eq114878
    | exact resolve eq114878 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114878
  have eq115153 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq115040
       have i₂ := eq3285 x
       grind)
    | exact superpose eq3285 eq115040
    | exact resolve eq115040 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115040
  have eq117065 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq115153
       grind)
    | exact superpose eq115153 eq16
    | exact resolve eq16 eq115153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117068 : (τ (σ y)) ≠ (τ (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq88767 (σ y) (σ x)
       have i₂ := eq115153
       grind)
    | exact superpose eq115153 eq88767
    | (have j0 := eq88767 (σ y) (σ x)
       grind)
    | exact resolve eq88767 eq115153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88767 eq115153
  have eq117071 : (σ y) = (M.op (σ x) (σ x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq117068
  have eq117076 : (σ y) = (σ (k x x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq117071
       have i₂ := eq3066 x
       grind)
    | exact superpose eq3066 eq117071
    | exact resolve eq117071 eq3066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3066 eq117071
  have eq117081 : (σ y) = (σ (M.op x x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq117076
       have i₂ := eq3285 x
       grind)
    | exact superpose eq3285 eq117076
    | exact resolve eq117076 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285 eq117076
  have eq117082 : (σ y) = (σ (M.op x x)) ∨ (τ (σ y)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x x) := by grind
  clear eq117081
  have eq117085 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq117082
       have i₂ := eq24 (σ y) x
       grind)
    | exact superpose eq24 eq117082
    | exact resolve eq117082 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq117082
  have eq117087 : y = (k y x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq117085
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq117085
    | exact resolve eq117085 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117085
  have eq117099 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1253 y x
       have i₂ := eq117087
       grind)
    | exact superpose eq117087 eq1253
    | (have j0 := eq1253 y x
       grind)
    | (have r₁ := eq1253 y x
       have r₂ := eq117087
       grind)
    | exact resolve eq1253 eq117087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1253 eq117087
  have eq117113 : y ≠ y ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq117099
  have eq117114 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq117113
  have eq118206 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq117065
       have i₂ := eq117114
       grind)
    | exact superpose eq117114 eq117065
    | exact resolve eq117065 eq117114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117065 eq117114
  have eq118207 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq118206
  have eq118208 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq118207
  have eq119389 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3957 x
       have i₂ := eq118208
       grind)
    | exact superpose eq118208 eq3957
    | exact resolve eq3957 eq118208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118208
  have eq119590 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq119389
       have r₂ := eq16
       grind)
    | exact resolve eq119389 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119389
  have eq119715 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq119590
       grind)
    | exact superpose eq119590 eq10
    | exact resolve eq10 eq119590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119590
  have eq119974 : y = (M.op x x) := by
    first
    | (have i₁ := eq119715
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq119715
    | exact resolve eq119715 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119715
  have eq121093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3957 x
       have i₂ := eq119974
       grind)
    | exact superpose eq119974 eq3957
    | exact resolve eq3957 eq119974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3957 eq119974
  have eq121294 : False := by grind
  exact eq121294

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation842 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law842 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq58 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq24
  have eq59 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq58
    | (have j0 := eq58 X0
       grind)
    | exact resolve eq58 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq54 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq54 X0
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq90 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq86 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq86 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq193 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq366 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X1 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq396 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq366 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq366
    | (have j0 := eq366 X0 X1
       grind)
    | exact resolve eq366 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq692 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq709 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq692 X0
       have i₂ := eq33 X0 X0
       grind)
    | exact superpose eq33 eq692
    | (have j0 := eq692 X0
       grind)
    | exact resolve eq692 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq692
  have eq711 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq193
       have i₂ := eq396 y x
       grind)
    | exact superpose eq396 eq193
    | (have j1 := eq396 (σ x) (σ y)
       grind)
    | (have r₁ := eq193
       have r₂ := eq396 y x
       grind)
    | (have r₁ := eq193
       have r₂ := eq396 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq193
       have r₂ := eq396 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq193 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq396
  have eq712 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq711
  have eq717 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq709 X0
       grind)
    | exact superpose eq709 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq709 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq709 X0
       grind)
    | exact resolve eq12 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq725 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq717 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq745 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq725 X0 X1
       grind)
    | exact superpose eq725 eq11
    | (have j1 := eq725 X0 X1
       grind)
    | exact resolve eq11 eq725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq757 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq745 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq745
    | (have j0 := eq745 X0 X0
       grind)
    | exact resolve eq745 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq818 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq757 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq819 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq818 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq855 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq819 X0
       grind)
    | exact superpose eq819 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq871 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq819 (σ X0)
       grind)
    | exact superpose eq819 eq15
    | exact resolve eq15 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq890 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq871 X0
       have i₂ := eq819 X0
       grind)
    | exact superpose eq819 eq871
    | exact resolve eq871 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819 eq871
  have eq58877 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
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
  have eq58878 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq58877
       have r₂ := eq890 x
       grind)
    | exact resolve eq58877 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58877
  have eq58879 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq58878
       have i₂ := eq890 x
       grind)
    | exact superpose eq890 eq58878
    | exact resolve eq58878 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58878
  have eq58881 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq58879
       grind)
    | exact superpose eq58879 eq10
    | exact resolve eq10 eq58879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58879
  have eq59007 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq58881
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq58881
    | exact resolve eq58881 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58881
  have eq59396 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq59007
       grind)
    | exact superpose eq59007 eq16
    | exact resolve eq16 eq59007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59007
  have eq59397 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq59396
       have r₂ := eq890 x
       grind)
    | exact resolve eq59396 eq890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890 eq59396
  have eq59456 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq59397
       grind)
    | exact superpose eq59397 eq10
    | exact resolve eq10 eq59397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59397
  have eq59589 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq59456
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq59456
    | exact resolve eq59456 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59456
  have eq59590 : x = (M.op x x) := by grind
  clear eq59589
  have eq60050 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq59590
       grind)
    | exact superpose eq59590 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq59590
       grind)
    | exact resolve eq12 eq59590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60069 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq855 x X0
       have i₂ := eq59590
       grind)
    | exact superpose eq59590 eq855
    | (have j0 := eq855 x X0
       grind)
    | exact resolve eq855 eq59590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq59590
  have eq60224 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq60069 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60069
  have eq60226 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq60050 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60050
  have eq62187 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq60224 (σ X0)
       grind)
    | exact superpose eq60224 eq15
    | exact resolve eq15 eq60224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60224
  have eq62288 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq62187 X0
       have i₂ := eq60226 X0
       grind)
    | exact superpose eq60226 eq62187
    | exact resolve eq62187 eq60226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60226 eq62187
  have eq69080 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62288 y
       grind)
    | exact superpose eq62288 eq16
    | (have r₁ := eq16
       have r₂ := eq62288 y
       grind)
    | exact resolve eq16 eq62288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62288
  have eq69286 : False := by grind
  exact eq69286
