import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq174 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq16 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq393 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq309 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq309
    | exact resolve eq309 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq540 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op x (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq552 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 X1 X3 x
       have i₂ := eq177 X1 X0 x
       grind)
    | (have i₁ := eq177 X0 X1 X0
       have i₂ := eq177 X0 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 x X2
       have i₂ := eq177 X0 x X1
       grind)
    | (have i₁ := eq177 X2 X2 X2
       have i₂ := eq177 X2 X1 X2
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq541 X0 x
       have i₂ := eq542 X0 x
       grind)
    | exact superpose eq542 eq541
    | exact resolve eq541 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq542
  have eq950 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq952 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1054 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq1056 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1059 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1057 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1057 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1057 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1124 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq13
    | exact resolve eq13 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1125 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op (M.op X1 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq16
    | exact resolve eq16 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 : G, x = (M.op (k X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq174
    | exact resolve eq174 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq1132 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq552 X1 X2 X0
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq552
    | exact resolve eq552 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq1135 : ∀ X0 : G, (M.op x (k X0 X0)) = (M.op (σ x) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq574 X0
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq574
    | exact resolve eq574 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq1140 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X1 X0
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq553
    | exact resolve eq553 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq1141 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (k X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1 X0
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq177
    | exact resolve eq177 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1142 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (k X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq16
    | exact resolve eq16 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1156 : ∀ X0 X1 : G, (M.op (k X1 X1) (M.op (k X0 X0) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1142 X0 X1
       have i₂ := eq1059 X1
       grind)
    | exact superpose eq1059 eq1142
    | exact resolve eq1142 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1157 : ∀ X0 X1 : G, (M.op (k X0 X0) X0) = (M.op (k X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1141 X0 X1
       have i₂ := eq1059 X1
       grind)
    | exact superpose eq1059 eq1141
    | exact resolve eq1141 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1160 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X2) = (M.op (k X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1132 X1 X0 X2
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq1132
    | exact resolve eq1132 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1173 : ∀ X0 : G, x = (M.op (σ (k X0 X0)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq1126 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1126
    | exact resolve eq1126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1382 : ∀ X0 X1 : G, (M.op x (σ (k X0 X0))) = (M.op (M.op X1 X1) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq1173 eq177
    | exact resolve eq177 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1173
  have eq1385 : ∀ X0 X1 : G, (M.op x (σ (k X0 X0))) = (M.op (k X1 X1) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1382 X0 X1
       have i₂ := eq1059 X1
       grind)
    | exact superpose eq1059 eq1382
    | exact resolve eq1382 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq1754 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X0)) (M.op (M.op X1 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1125 (σ X0) X1 X2
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1125
    | exact resolve eq1125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1788 : ∀ X0 X1 X2 : G, (k X2 X2) = (M.op (k X1 X1) (M.op X0 (k X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1125 X1 (k X2 X2) (M.op (M.op X0 x) X0)
       have i₂ := eq1125 X2 X0 x
       grind)
    | exact superpose eq1125 eq1125
    | exact resolve eq1125 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq2041 : ∀ X0 X1 : G, (σ X0) = (M.op (k X1 X1) (M.op (σ (k X0 X0)) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1156 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1156
    | exact resolve eq1156 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq2089 : ∀ X0 X1 : G, (M.op (k X1 X1) X1) = (M.op (σ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1157 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1157
    | exact resolve eq1157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq2507 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq950
       grind)
    | exact superpose eq950 eq40
    | exact resolve eq40 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq2508 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2507
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2507
    | exact resolve eq2507 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq2510 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2508
    | exact resolve eq2508 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2508
  have eq2512 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2510
       have i₂ := eq1059 x
       grind)
    | exact superpose eq1059 eq2510
    | exact resolve eq2510 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510
  have eq2514 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq2512
       have i₂ := eq1059 y
       grind)
    | exact superpose eq1059 eq2512
    | exact resolve eq2512 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq2516 : ∀ X0 : G, (M.op x (σ (k X0 X0))) = (M.op (σ x) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1135 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1135
    | exact resolve eq1135 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq2753 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (M.op (σ (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1160 X1 (σ X0) X2
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1160
    | exact resolve eq1160 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2754 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (M.op (τ (k X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1160 X1 (τ X0) X2
       have i₂ := eq393 X0 X0
       grind)
    | exact superpose eq393 eq1160
    | exact resolve eq1160 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq3869 : ∀ X0 X1 : G, (M.op X0 (σ (k X1 X1))) = (M.op (k (σ (k X1 X1)) (σ (k X1 X1))) (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1140 (σ (k X1 X1)) (M.op (M.op X0 x) X0)
       have i₂ := eq1754 X1 X0 x
       grind)
    | exact superpose eq1754 eq1140
    | exact resolve eq1140 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140 eq1754
  have eq3870 : ∀ X0 X1 : G, (M.op x (σ (k X1 X1))) = (M.op X0 (σ (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3869 X0 X1
       have i₂ := eq1385 X1 (σ (k X1 X1))
       grind)
    | exact superpose eq1385 eq3869
    | exact resolve eq3869 eq1385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385 eq3869
  have eq4306 : (M.op x y) ≠ (k x x) ∨ y = (M.op y y) ∨ (k x x) = (k x y) := by
    first
    | (have i₁ := eq1054
       have i₂ := eq1059 x
       grind)
    | exact superpose eq1059 eq1054
    | exact resolve eq1054 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054
  have eq4307 : (M.op x y) ≠ (k x x) ∨ y = (k y y) ∨ (k x x) = (k x y) := by
    first
    | (have i₁ := eq4306
       have i₂ := eq1059 y
       grind)
    | exact superpose eq1059 eq4306
    | exact resolve eq4306 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4306
  have eq4322 : ∀ X0 X1 : G, (M.op (k X1 X1) X1) = (M.op (σ (σ (k X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2089 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq2089
    | exact resolve eq2089 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq5004 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1056
       have i₂ := eq1059 sF2
       grind)
    | exact superpose eq1059 eq1056
    | exact resolve eq1056 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq5005 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq5004
       have i₂ := eq1059 sF3
       grind)
    | exact superpose eq1059 eq5004
    | exact resolve eq5004 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5004
  have eq5473 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (M.op (σ (σ (k X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2753 (σ X0) X1 X2
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq2753
    | exact resolve eq2753 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2753
  have eq5744 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (M.op (τ (τ (k X0 X0))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2754 (τ X0) X1 X2
       have i₂ := eq393 X0 X0
       grind)
    | exact superpose eq393 eq2754
    | exact resolve eq2754 eq393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq6944 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq540 X0 (M.op X1 X1) X3
       have i₂ := eq540 X0 X1 X1
       grind)
    | (have i₁ := eq540 X0 (M.op X1 X1) X3
       have i₂ := eq540 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq540 eq540
    | exact resolve eq540 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq7240 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (k X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (k X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6944 X0 X0 X2 X3
       have i₂ := eq1059 X0
       grind)
    | exact superpose eq1059 eq6944
    | exact resolve eq6944 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6944
  have eq7325 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (k X1 X1))) = (M.op (k X2 X2) (M.op X0 (k X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq7240 X0 X1 X2 X3
       have i₂ := eq1059 X2
       grind)
    | exact superpose eq1059 eq7240
    | exact resolve eq7240 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7240
  have eq7351 : ∀ X0 X1 X3 : G, (k X1 X1) = (M.op X3 (M.op X0 (k X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7325 X0 X1 x X3
       have i₂ := eq1788 X0 x X1
       grind)
    | exact superpose eq1788 eq7325
    | exact resolve eq7325 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788 eq7325
  have eq8439 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7351 (k X0 X0) X0 X1
       have i₂ := eq1059 (k X0 X0)
       grind)
    | exact superpose eq1059 eq7351
    | exact resolve eq7351 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7351
  have eq75937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq2514 eq952
    | exact resolve eq952 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75946 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | (have r₁ := eq75937
       have r₂ := eq27
       grind)
    | exact resolve eq75937 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75937
  have eq75953 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq75946
       have i₂ := eq1059 sF2
       grind)
    | exact superpose eq1059 eq75946
    | exact resolve eq75946 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75946
  have eq75956 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq75953
       have i₂ := eq1059 sF3
       grind)
    | exact superpose eq1059 eq75953
    | exact resolve eq75953 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75953
  have eq101704 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq75956 eq5005
    | (have r₁ := eq5005
       have r₂ := eq75956
       grind)
    | exact resolve eq5005 eq75956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5005 eq75956
  have eq101705 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by grind
  clear eq101704
  have eq101706 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by grind
  clear eq101705
  have eq101707 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq2514 eq101706
    | exact resolve eq101706 eq2514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514 eq101706
  have eq101708 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | (have r₁ := eq101707
       have r₂ := eq27
       grind)
    | exact resolve eq101707 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101707
  have eq101713 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq101708 eq152
    | exact resolve eq152 eq101708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101708
  have eq102093 : y = (k y y) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq101713
    | exact resolve eq101713 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101713
  have eq102094 : (M.op x y) = (k x x) ∨ y = (k y y) := by grind
  clear eq102093
  have eq102140 : (M.op x y) ≠ (M.op x y) ∨ y = (k y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq4307
       have i₂ := eq102094
       grind)
    | exact superpose eq102094 eq4307
    | (have r₁ := eq4307
       have r₂ := eq102094
       grind)
    | exact resolve eq4307 eq102094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4307
  have eq102146 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq102094
       grind)
    | exact superpose eq102094 eq39
    | exact resolve eq39 eq102094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq102094
  have eq102425 : (M.op x y) ≠ (M.op x y) ∨ y = (k y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq102140
  have eq102426 : (M.op x y) = (k x y) ∨ y = (k y y) := by grind
  clear eq102425
  have eq102520 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq102146
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102146
    | exact resolve eq102146 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102146
  have eq102562 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq102520
    | exact resolve eq102520 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102520
  have eq102579 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq102426
       grind)
    | exact superpose eq102426 eq40
    | exact resolve eq40 eq102426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102426
  have eq102581 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq102579
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102579
    | exact resolve eq102579 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq102579
  have eq102585 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq102581
    | exact resolve eq102581 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102581
  have eq103150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq102585 eq952
    | exact resolve eq952 eq102585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq102585
  have eq103159 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq103150
       have r₂ := eq27
       grind)
    | exact resolve eq103150 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103150
  have eq103165 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq103159
       have i₂ := eq1059 sF2
       grind)
    | exact superpose eq1059 eq103159
    | exact resolve eq103159 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103159
  have eq103167 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq103165
       have i₂ := eq1059 sF3
       grind)
    | exact superpose eq1059 eq103165
    | exact resolve eq103165 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103165
  have eq103169 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq102562 eq103167
    | exact resolve eq103167 eq102562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102562 eq103167
  have eq103171 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq103169
       have r₂ := eq27
       grind)
    | exact resolve eq103169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103169
  have eq103177 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) := by
    first
    | exact superpose eq103171 eq152
    | exact resolve eq152 eq103171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq103171
  have eq103605 : y = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq103177
    | exact resolve eq103177 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq103177
  have eq103606 : y = (k y y) := by grind
  clear eq103605
  have eq103685 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq1124 y x
       have i₂ := eq103606
       grind)
    | exact superpose eq103606 eq1124
    | (have r₁ := eq1124 y x
       have r₂ := eq103606
       grind)
    | exact resolve eq1124 eq103606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq103772 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (τ y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2754 y X0 X1
       have i₂ := eq103606
       grind)
    | exact superpose eq103606 eq2754
    | exact resolve eq2754 eq103606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2754
  have eq103816 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (σ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq4322 y X0
       have i₂ := eq103606
       grind)
    | exact superpose eq103606 eq4322
    | exact resolve eq4322 eq103606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4322
  have eq103840 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5473 y X0 X1
       have i₂ := eq103606
       grind)
    | exact superpose eq103606 eq5473
    | exact resolve eq5473 eq103606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5473
  have eq103841 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (τ (τ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5744 y X0 X1
       have i₂ := eq103606
       grind)
    | exact superpose eq103606 eq5744
    | exact resolve eq5744 eq103606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5744
  have eq103900 : ∀ X0 : G, y = (M.op X0 (k y y)) := by
    intro X0
    first
    | (have i₁ := eq8439 y x
       have i₂ := eq103606
       grind)
    | exact superpose eq103606 eq8439
    | exact resolve eq8439 eq103606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8439
  have eq103962 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq103685 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103685
  have eq103982 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq103900 X0
       have i₂ := eq103606
       grind)
    | exact superpose eq103606 eq103900
    | exact resolve eq103900 eq103606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103606 eq103900
  have eq104005 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (σ (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq103840 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq103840
    | (have j0 := eq103840 X0 X1
       grind)
    | exact resolve eq103840 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103840
  have eq104015 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op (σ (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq103816 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq103816
    | (have j0 := eq103816 X0
       grind)
    | exact resolve eq103816 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103816
  have eq104083 : ∀ X1 : G, (M.op (σ (σ y)) X1) = (M.op (τ y) X1) := by
    intro X1
    first
    | (have i₁ := eq104005 x X1
       have i₂ := eq103772 x X1
       grind)
    | exact superpose eq103772 eq104005
    | exact resolve eq104005 eq103772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103772 eq104005
  have eq104088 : ∀ X0 : G, (M.op (σ (σ y)) X0) = (M.op (τ (τ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq104015 X0
       have i₂ := eq103841 X0 X0
       grind)
    | exact superpose eq103841 eq104015
    | exact resolve eq104015 eq103841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104015
  have eq104107 : ∀ X0 : G, (M.op (τ y) X0) = (M.op (τ (τ y)) X0) := by
    intro X0
    first
    | exact superpose eq104083 eq104088
    | exact resolve eq104088 eq104083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104083 eq104088
  have eq104197 : ∀ X0 : G, (σ y) = (M.op (k X0 X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2041 y X0
       have i₂ := eq103962 y
       grind)
    | exact superpose eq103962 eq2041
    | exact resolve eq2041 eq103962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041
  have eq104416 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 y
       have i₂ := eq103962 (τ X0)
       grind)
    | exact superpose eq103962 eq34
    | exact resolve eq34 eq103962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq103962
  have eq104486 : ∀ X0 : G, (σ y) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq104416 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq104416
    | (have j0 := eq104416 X0
       grind)
    | exact resolve eq104416 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104416
  have eq104572 : (σ y) = (M.op (τ (τ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq104197 x
       have i₂ := eq103841 x (M.op (σ y) (σ y))
       grind)
    | exact superpose eq103841 eq104197
    | exact resolve eq104197 eq103841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103841 eq104197
  have eq104630 : (σ y) = (M.op (τ y) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq104572
       have i₂ := eq104107 (M.op (σ y) (σ y))
       grind)
    | exact superpose eq104107 eq104572
    | exact resolve eq104572 eq104107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104107 eq104572
  have eq104645 : (σ y) = (M.op (τ y) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq104630
       have i₂ := eq1059 (σ y)
       grind)
    | exact superpose eq1059 eq104630
    | exact resolve eq104630 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059 eq104630
  have eq104655 : (σ y) = (M.op (τ y) (σ (k y y))) := by
    first
    | (have i₁ := eq104645
       have i₂ := eq10 y y
       grind)
    | exact superpose eq10 eq104645
    | exact resolve eq104645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104645
  have eq104658 : (σ y) = (M.op x (σ (k y y))) := by
    first
    | (have i₁ := eq104655
       have i₂ := eq3870 (τ y) y
       grind)
    | exact superpose eq3870 eq104655
    | exact resolve eq104655 eq3870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3870 eq104655
  have eq104661 : (σ y) = (M.op (σ x) (σ (k y y))) := by
    first
    | (have i₁ := eq104658
       have i₂ := eq2516 y
       grind)
    | exact superpose eq2516 eq104658
    | exact resolve eq104658 eq2516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2516 eq104658
  have eq104664 : (σ y) = (M.op (σ x) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq104661
       have i₂ := eq40 y
       grind)
    | exact superpose eq40 eq104661
    | exact resolve eq104661 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq104661
  have eq104665 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq104486 eq104664
    | exact resolve eq104664 eq104486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104486 eq104664
  have eq104666 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq104665
    | exact resolve eq104665 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq104665
  have eq104667 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq104666
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq104666
    | exact resolve eq104666 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104666
  have eq104668 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq104667 eq27
    | exact resolve eq27 eq104667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq104667
  have eq105076 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq103982 x
       grind)
    | exact superpose eq103982 eq18
    | (have j1 := eq103982 x
       grind)
    | exact resolve eq18 eq103982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq103982
  have eq105200 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq105076
       grind)
    | exact superpose eq105076 eq24
    | exact resolve eq24 eq105076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq105076
  have eq105256 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq105200 eq20
    | exact resolve eq20 eq105200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq105200
  have eq105406 : False := by grind
  exact eq105406

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq9 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq52 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 X2)) = (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 (M.op X1 X2) X3 X1
       have i₂ := eq52 X1 X0 X2
       grind)
    | (have i₁ := eq52 (M.op X1 X1) X1 X0
       have i₂ := eq52 X0 X1 X2
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq52 X1 X3 x
       have i₂ := eq52 X1 X0 x
       grind)
    | (have i₁ := eq52 X0 X1 X0
       have i₂ := eq52 X0 X0 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 X1) X0) x X2
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X0 x X2
       have i₂ := eq52 X0 x X1
       grind)
    | (have i₁ := eq52 X2 X2 X2
       have i₂ := eq52 X2 X1 X2
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 x
       have i₂ := eq52 X1 X0 x
       grind)
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq52 X0 X0 X2
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq51 (M.op X0 X0) (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq63 X3 X1 x
       have i₂ := eq63 X0 X1 x
       grind)
    | (have i₁ := eq63 X0 X1 X3
       have i₂ := eq63 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X0 (M.op X1 X1) X3
       have i₂ := eq63 X0 X1 X1
       grind)
    | (have i₁ := eq63 X0 (M.op X1 X1) X3
       have i₂ := eq63 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) X3
       have i₂ := eq63 X0 X1 X1
       grind)
    | (have i₁ := eq9 X0 (M.op X1 X1) X2
       have i₂ := eq63 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq249 X0 X1 x X3
       have i₂ := eq51 X0 x X1
       grind)
    | exact superpose eq51 eq249
    | exact resolve eq249 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq249
  have eq489 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq490 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq489 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq489
    | (have j0 := eq489 (σ X0) (σ X1)
       grind)
    | exact resolve eq489 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq489 X0 (τ X1)
       grind)
    | exact superpose eq489 eq18
    | (have j1 := eq489 X0 (τ X1)
       grind)
    | exact resolve eq18 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq490 x y
       grind)
    | exact superpose eq490 eq16
    | (have j1 := eq490 x y
       grind)
    | exact resolve eq16 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (σ X0) X2
       have i₂ := eq490 X0 X0
       grind)
    | exact superpose eq490 eq52
    | (have j1 := eq490 X0 X0
       grind)
    | exact resolve eq52 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (σ (k X0 X0)) X2)) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 (σ X0) X2 X1
       have i₂ := eq490 X0 X0
       grind)
    | exact superpose eq490 eq72
    | (have j1 := eq490 X0 X0
       grind)
    | exact resolve eq72 eq490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq1506 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) = (M.op (M.op (M.op (M.op (M.op X0 X1) X0) X2) X3) (M.op (M.op (M.op X0 X1) X0) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 (M.op (M.op (M.op X0 X1) X0) X2) X3 (M.op (M.op X0 X1) X0)
       have i₂ := eq69 X0 X1 X2
       grind)
    | exact superpose eq69 eq70
    | exact resolve eq70 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1867 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X0 X0) (M.op X1 X2))) = (M.op (M.op (M.op X5 X5) (M.op (M.op X4 X4) X1)) (M.op (M.op X0 X0) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq65 X0 (M.op X3 X3) (M.op X1 X2) X3
       have i₂ := eq65 X0 X1 X2 X3
       grind)
    | (have i₁ := eq65 X0 (M.op (M.op X0 X0) X1) (M.op X1 X2) X3
       have i₂ := eq65 X0 X1 X2 X3
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2056 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op (M.op X0 X0) (M.op X1 X2))) = (M.op X1 (M.op (M.op X0 X0) (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1867 X0 X1 X2 X3 x x
       have i₂ := eq72 x X1 x
       grind)
    | exact superpose eq72 eq1867
    | exact resolve eq1867 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867
  have eq2072 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X0) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2056 X0 X1 X2 x
       have i₂ := eq72 X0 (M.op X1 X2) x
       grind)
    | exact superpose eq72 eq2056
    | exact resolve eq2056 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2056
  have eq2110 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X3 X3) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2072 X0 (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)
       have i₂ := eq69 X0 X1 X2
       grind)
    | exact superpose eq69 eq2072
    | exact resolve eq2072 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072
  have eq2541 : ∀ X0 X1 X2 : G, (k (σ (M.op X2 X2)) X1) = (σ (M.op (M.op X0 X0) (τ X1))) ∨ (τ X1) = (M.op (τ X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq496 (M.op X2 X2) X1
       have i₂ := eq68 X2 (τ X1) X0
       grind)
    | (have i₁ := eq496 (M.op X2 X2) X1
       have i₂ := eq68 X0 (τ X1) X2
       grind)
    | exact superpose eq68 eq496
    | (have j0 := eq496 (M.op X2 X2) X1
       grind)
    | exact resolve eq496 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2545 : ∀ X0 X1 X2 : G, (σ (M.op (M.op (τ X0) X1) (τ X0))) = (k (σ (M.op (τ X0) X2)) X0) ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq496 (M.op (τ X0) X2) X0
       have i₂ := eq70 (τ X0) X1 X2
       grind)
    | (have i₁ := eq496 (M.op (τ X0) X2) X0
       have i₂ := eq70 (τ X0) X2 X1
       grind)
    | exact superpose eq70 eq496
    | (have j0 := eq496 (M.op (τ X0) X2) X0
       grind)
    | exact resolve eq496 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq496
  have eq2573 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq602
       have i₂ := eq489 x y
       grind)
    | exact superpose eq489 eq602
    | (have j1 := eq489 (σ x) (σ y)
       grind)
    | exact resolve eq602 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq2576 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq2573
  have eq2579 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ x)
       have i₂ := eq2576
       grind)
    | exact superpose eq2576 eq9
    | exact resolve eq9 eq2576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3032 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (k (σ (τ X0)) X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq607 (τ X0) X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq607
    | (have j0 := eq607 (τ X0) X1 X2
       grind)
    | exact resolve eq607 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3089 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op (σ (k X0 X0)) X1) (M.op X1 X2)) X3) (M.op (M.op (σ (k X0 X0)) X1) (M.op X1 X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq69 (M.op X1 X2) X1 X2
       have i₂ := eq607 X0 X1 X2
       grind)
    | exact superpose eq607 eq69
    | (have j1 := eq607 X0 X1 X2
       grind)
    | exact resolve eq69 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq607
  have eq3149 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (k X0 X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3032 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3032
    | (have j0 := eq3032 X0 X1 X2
       grind)
    | exact resolve eq3032 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3032
  have eq3161 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3149 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3149
    | (have j0 := eq3149 X0 X1 X2
       grind)
    | exact resolve eq3149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3149
  have eq5907 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X1 (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq221 X0 X1
       have i₂ := eq314 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq314 eq221
    | (have j0 := eq221 X0 X1
       grind)
    | exact resolve eq221 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq5933 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (k X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5907 X1 X1
       have i₂ := eq63 X0 X1 X1
       grind)
    | (have i₁ := eq5907 X1 X1
       have i₂ := eq63 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq63 eq5907
    | exact resolve eq5907 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq5907
  have eq6376 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X3) (M.op (M.op X4 X4) X2)) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2110 X2 (M.op X1 X1) X3 X4
       have i₂ := eq239 X2 X1 X0
       grind)
    | (have i₁ := eq2110 X2 (M.op X1 X1) X3 X4
       have i₂ := eq239 X0 X1 X2
       grind)
    | exact superpose eq239 eq2110
    | exact resolve eq2110 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6486 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X2) X0) X3) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2110 X0 X2 X3 x
       have i₂ := eq52 X0 x X1
       grind)
    | (have i₁ := eq2110 X2 X1 X2 X2
       have i₂ := eq52 X2 X1 X2
       grind)
    | exact superpose eq52 eq2110
    | exact resolve eq2110 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110
  have eq7880 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (k X0 X0) X1)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 x
       have i₂ := eq3161 X0 X1 x
       grind)
    | exact superpose eq3161 eq9
    | (have j1 := eq3161 X0 X1 X2
       grind)
    | exact resolve eq9 eq3161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161
  have eq8071 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X3) (M.op (M.op X2 X4) X2)) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq6486 X2 X4 (M.op X1 X1) X3
       have i₂ := eq239 X2 X1 X0
       grind)
    | (have i₁ := eq6486 X2 X4 (M.op X1 X1) X3
       have i₂ := eq239 X0 X1 X2
       grind)
    | exact superpose eq239 eq6486
    | exact resolve eq6486 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11091 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op X1 (M.op X2 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq314 X0 (M.op (k X0 X0) (k X0 X0)) x
       have i₂ := eq7880 X0 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq7880 eq314
    | (have j1 := eq7880 X0 X1 X2
       grind)
    | exact resolve eq314 eq7880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7880
  have eq13874 : ∀ X1 X2 : G, (M.op (σ y) (M.op (M.op X1 X2) X1)) = X1 ∨ y = (M.op y x) := by
    intro X1 X2
    first
    | (have i₁ := eq274 (M.op x x) (σ y) X1 X2
       have i₂ := eq2579 x
       grind)
    | exact superpose eq2579 eq274
    | exact resolve eq274 eq2579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13905 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 (M.op (σ y) (σ y)) x
       have i₂ := eq2579 (σ y)
       grind)
    | exact superpose eq2579 eq239
    | exact resolve eq239 eq2579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13906 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (M.op (M.op X1 X2) X1)) = X1 ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq274 X0 (M.op (σ y) (σ y)) X1 X2
       have i₂ := eq2579 (σ y)
       grind)
    | exact superpose eq2579 eq274
    | exact resolve eq274 eq2579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13914 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (σ y))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0 (M.op (σ y) (σ y)) x
       have i₂ := eq2579 (σ y)
       grind)
    | exact superpose eq2579 eq314
    | exact resolve eq314 eq2579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq15515 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = X0 ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq13874 X0 (M.op x (σ y))
       have i₂ := eq13914 X0 x
       grind)
    | exact superpose eq13914 eq13874
    | exact resolve eq13874 eq13914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13874 eq13914
  have eq15700 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq15515 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15515
  have eq15718 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq15700 (σ x)
       have i₂ := eq2576
       grind)
    | exact superpose eq2576 eq15700
    | exact resolve eq15700 eq2576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15700
  have eq15803 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq15718
  have eq51691 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) (M.op (M.op X0 (σ y)) X2)) = X2 ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13906 X1 X2 (σ y)
       have i₂ := eq13905 X2 X0
       grind)
    | (have i₁ := eq13906 X1 X2 (σ y)
       have i₂ := eq13905 X0 X2
       grind)
    | exact superpose eq13905 eq13906
    | exact resolve eq13906 eq13905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13905 eq13906
  have eq52326 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ y)) (M.op (M.op X0 (σ y)) X2)) = X2 ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq51691 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51691
  have eq63657 : ∀ X0 X1 X2 : G, (k (τ (σ (M.op X2 X2))) X1) = (τ (σ (M.op (M.op X0 X0) (τ (σ X1))))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ (M.op X2 X2)) X1
       have i₂ := eq2541 X0 (σ X1) X2
       grind)
    | exact superpose eq2541 eq22
    | (have j1 := eq2541 X0 (σ X1) X2
       grind)
    | exact resolve eq22 eq2541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2541
  have eq63727 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (τ (σ X1))) = (k (τ (σ (M.op X2 X2))) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63657 X0 X1 X2
       have i₂ := eq10 (M.op (M.op X0 X0) (τ (σ X1)))
       grind)
    | exact superpose eq10 eq63657
    | (have j0 := eq63657 X0 X1 X2
       grind)
    | exact resolve eq63657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63657
  have eq63825 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (τ (σ X1))) = (k (M.op X2 X2) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63727 X0 X1 X2
       have i₂ := eq10 (M.op X2 X2)
       grind)
    | exact superpose eq10 eq63727
    | (have j0 := eq63727 X0 X1 X2
       grind)
    | exact resolve eq63727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63727
  have eq63885 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k (M.op X2 X2) X1) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63825 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq63825
    | (have j0 := eq63825 X0 X1 X2
       grind)
    | exact resolve eq63825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63825
  have eq63910 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k (M.op X2 X2) X1) ∨ (M.op X1 (M.op X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63885 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63885
    | (have j0 := eq63885 X0 X1 X2
       grind)
    | exact resolve eq63885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63885
  have eq101679 : ∀ X0 X1 X2 : G, (τ (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) X2))) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (M.op (τ (σ X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ (M.op (τ (σ X0)) X2)) X0
       have i₂ := eq2545 (σ X0) X1 X2
       grind)
    | exact superpose eq2545 eq22
    | (have j1 := eq2545 (σ X0) X1 X2
       grind)
    | exact resolve eq22 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2545
  have eq101714 : ∀ X0 X1 X2 : G, (τ (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))))) = (k (M.op (τ (σ X0)) X2) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (M.op (τ (σ X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101679 X0 X1 X2
       have i₂ := eq10 (M.op (τ (σ X0)) X2)
       grind)
    | exact superpose eq10 eq101679
    | (have j0 := eq101679 X0 X1 X2
       grind)
    | exact resolve eq101679 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101679
  have eq101757 : ∀ X0 X1 X2 : G, (k (M.op X0 X2) X0) = (τ (σ (M.op (M.op X0 X1) X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (M.op (τ (σ X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101714 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101714
    | (have j0 := eq101714 X0 X1 X2
       grind)
    | exact resolve eq101714 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101714
  have eq101786 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X2) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (M.op (τ (σ X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101757 X0 X1 X2
       have i₂ := eq10 (M.op (M.op X0 X1) X0)
       grind)
    | exact superpose eq10 eq101757
    | (have j0 := eq101757 X0 X1 X2
       grind)
    | exact resolve eq101757 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101757
  have eq101809 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (k (M.op X0 X2) X0) ∨ (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101786 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq101786
    | (have j0 := eq101786 X0 X1 X2
       grind)
    | exact resolve eq101786 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101786
  have eq114017 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (k (M.op X0 X0) X1)) = X1 ∨ (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X1
       have i₂ := eq63910 X1 X1 X0
       grind)
    | exact superpose eq63910 eq9
    | (have j1 := eq63910 X0 X1 X0
       grind)
    | exact resolve eq9 eq63910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63910
  have eq137890 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (k (M.op X0 (M.op X1 X1)) X3)) = X3 ∨ (M.op X3 (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq114017 (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1))) X1 X2
       have i₂ := eq6376 X0 X1 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq6376 eq114017
    | exact resolve eq114017 eq6376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6376 eq114017
  have eq138286 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (k (M.op X0 (M.op X1 X1)) X3)) = X3 ∨ (M.op X1 X1) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq137890 X0 X1 X2 X3
       have i₂ := eq314 X0 X1 X3
       grind)
    | exact superpose eq314 eq137890
    | (have j0 := eq137890 X0 X1 X2 X3
       grind)
    | exact resolve eq137890 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137890
  have eq164892 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X1))) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) ∨ (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11091 (M.op X0 (M.op X1 X1)) X2 (M.op x x)
       have i₂ := eq138286 X0 X1 x (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq138286 eq11091
    | (have j0 := eq11091 (M.op X0 (M.op X1 X1)) X1 X2
       have j1 := eq138286 X0 (M.op X0 (M.op X1 X1)) X2 (M.op X0 (M.op X1 X1))
       grind)
    | exact resolve eq11091 eq138286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11091
  have eq165012 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) ∨ (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq164892 X0 X1 x
       have i₂ := eq314 X0 X1 x
       grind)
    | exact superpose eq314 eq164892
    | (have j0 := eq164892 X0 X1 x
       grind)
    | exact resolve eq164892 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164892
  have eq165102 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) ∨ (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq165012 X0 X1
       have j1 := eq5933 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | (have r₁ := eq165012 (M.op X1 X1) X1
       have r₂ := eq5933 (M.op (M.op X1 X1) (M.op X1 X1)) (M.op X1 X1) x
       grind)
    | (have r₁ := eq165012 X0 X1
       have r₂ := eq5933 X0 X1 x
       grind)
    | exact resolve eq165012 eq5933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165012
  have eq165122 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq165102 X0 X1
       have i₂ := eq314 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq314 eq165102
    | (have j0 := eq165102 X0 X1
       grind)
    | exact resolve eq165102 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165102
  have eq165125 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq165122 X0 X1
       have j1 := eq5933 X0 X1 (M.op X0 (M.op X1 X1))
       grind)
    | (have r₁ := eq165122 X0 X1
       have r₂ := eq5933 X0 X1 x
       grind)
    | exact resolve eq165122 eq5933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5933 eq165122
  have eq165234 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq165125 X0 (M.op (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)))
       have i₂ := eq8071 X0 X1 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq8071 eq165125
    | exact resolve eq165125 eq8071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8071
  have eq165600 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq165234 X0 X1 x
       have i₂ := eq314 X0 X1 x
       grind)
    | exact superpose eq314 eq165234
    | exact resolve eq165234 eq314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165234
  have eq165895 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq165600 X0 (M.op (M.op X0 (σ y)) (σ y))
       have i₂ := eq52326 X0 (M.op X0 (σ y)) (σ y)
       grind)
    | exact superpose eq52326 eq165600
    | exact resolve eq165600 eq52326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52326
  have eq165929 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq165600 X0 (σ y)
       have i₂ := eq15803
       grind)
    | exact superpose eq15803 eq165600
    | exact resolve eq165600 eq15803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165953 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq314 x X0 X1
       have i₂ := eq165600 x X0
       grind)
    | exact superpose eq165600 eq314
    | exact resolve eq314 eq165600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166649 : ∀ X0 : G, (M.op X0 (σ x)) = (σ (k x x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq165929 X0
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq165929
    | exact resolve eq165929 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165929
  have eq166668 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k y y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq165895 X0
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq165895
    | exact resolve eq165895 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165895
  have eq172947 : (σ y) = (σ (k x x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2576
       have i₂ := eq166649 (σ y)
       grind)
    | exact superpose eq166649 eq2576
    | exact resolve eq2576 eq166649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576 eq166649
  have eq173127 : (σ y) = (σ (k x x)) ∨ y = (M.op y x) := by grind
  clear eq172947
  have eq173692 : (τ (σ y)) = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq173127
       grind)
    | exact superpose eq173127 eq10
    | exact resolve eq10 eq173127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173127
  have eq173785 : y = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq173692
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq173692
    | exact resolve eq173692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173692
  have eq174535 : (σ x) = (σ (k y y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq15803
       have i₂ := eq166668 (σ y)
       grind)
    | exact superpose eq166668 eq15803
    | exact resolve eq15803 eq166668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15803 eq166668
  have eq174722 : (σ x) = (σ (k y y)) ∨ y = (M.op y x) := by grind
  clear eq174535
  have eq174912 : (τ (σ x)) = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq174722
       grind)
    | exact superpose eq174722 eq10
    | exact resolve eq10 eq174722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174722
  have eq175005 : y = (M.op y x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq174912
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq174912
    | exact resolve eq174912 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174912
  have eq175006 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq175005
       grind)
    | exact superpose eq175005 eq9
    | exact resolve eq9 eq175005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178243 : ∀ X1 X2 : G, (M.op y (M.op (M.op X1 X2) X1)) = X1 ∨ x = (k y y) := by
    intro X1 X2
    first
    | (have i₁ := eq274 (M.op x x) y X1 X2
       have i₂ := eq175006 x
       grind)
    | exact superpose eq175006 eq274
    | exact resolve eq274 eq175006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq178290 : (k y y) = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq165125 (M.op x x) y
       have i₂ := eq175006 x
       grind)
    | exact superpose eq175006 eq165125
    | exact resolve eq165125 eq175006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178494 : ∀ X0 : G, y = (M.op X0 (k y y)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq165953 (M.op y y) x
       have i₂ := eq175006 y
       grind)
    | exact superpose eq175006 eq165953
    | exact resolve eq165953 eq175006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175006
  have eq180413 : x ≠ (M.op y y) ∨ x = (k y y) := by grind
  clear eq178290
  have eq188076 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 ∨ x = (k y y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq178243 X0 (k y y)
       have i₂ := eq178494 X0
       grind)
    | exact superpose eq178494 eq178243
    | exact resolve eq178243 eq178494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178243 eq178494
  have eq188689 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 ∨ x = (k y y) := by
    intro X0
    first
    | (have j0 := eq188076 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188076
  have eq188736 : x = (M.op y y) ∨ x = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq188689 x
       have i₂ := eq175005
       grind)
    | exact superpose eq175005 eq188689
    | exact resolve eq188689 eq175005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175005 eq188689
  have eq188958 : x = (M.op y y) ∨ x = (k y y) := by grind
  clear eq188736
  have eq188963 : x = (k y y) := by
    first
    | (have r₁ := eq188958
       have r₂ := eq180413
       grind)
    | exact resolve eq188958 eq180413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180413 eq188958
  have eq188966 : y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq188963
       have i₂ := eq489 y y
       grind)
    | exact superpose eq489 eq188963
    | (have j1 := eq489 y y
       grind)
    | exact resolve eq188963 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq189262 : ∀ X0 : G, (k y y) = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq165600 X0 y
       have i₂ := eq188966
       grind)
    | exact superpose eq188966 eq165600
    | exact resolve eq165600 eq188966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188966
  have eq189393 : ∀ X0 : G, x = (M.op y y) ∨ x = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq189262 X0
       have i₂ := eq188963
       grind)
    | exact superpose eq188963 eq189262
    | exact resolve eq189262 eq188963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189262
  have eq190341 : x ≠ x ∨ x = (M.op y y) := by
    first
    | (have j0 := eq189393 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189393
  have eq190342 : x = (M.op y y) := by grind
  clear eq190341
  have eq190363 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 y X1
       have i₂ := eq190342
       grind)
    | exact superpose eq190342 eq9
    | exact resolve eq9 eq190342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190367 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 y X1
       have i₂ := eq190342
       grind)
    | exact superpose eq190342 eq52
    | exact resolve eq52 eq190342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq190371 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 y X0 X1
       have i₂ := eq190342
       grind)
    | exact superpose eq190342 eq68
    | exact resolve eq68 eq190342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq190380 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 y x
       have i₂ := eq190342
       grind)
    | exact superpose eq190342 eq239
    | exact resolve eq239 eq190342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq190389 : ∀ X0 X1 : G, x = (M.op X0 (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq314 X0 y x
       have i₂ := eq190342
       grind)
    | exact superpose eq190342 eq314
    | exact resolve eq314 eq190342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314
  have eq190544 : ∀ X0 : G, (M.op X0 x) = (k x x) := by
    intro X0
    first
    | (have i₁ := eq165600 X0 y
       have i₂ := eq190342
       grind)
    | exact superpose eq190342 eq165600
    | exact resolve eq165600 eq190342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190342
  have eq192948 : ∀ X0 : G, y = (M.op y x) ∨ y = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq190544 X0
       have i₂ := eq173785
       grind)
    | exact superpose eq173785 eq190544
    | exact resolve eq190544 eq173785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173785 eq190544
  have eq194186 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq190363 X0 (M.op x x)
       have i₂ := eq190389 X0 x
       grind)
    | exact superpose eq190389 eq190363
    | exact resolve eq190363 eq190389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194222 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 x) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190363 X1 x
       have i₂ := eq190380 X0 X1
       grind)
    | (have i₁ := eq190363 X1 x
       have i₂ := eq190380 X1 X0
       grind)
    | exact superpose eq190380 eq190363
    | exact resolve eq190363 eq190380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190363
  have eq195231 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq190367 X1 x
       have i₂ := eq190380 X0 X1
       grind)
    | (have i₁ := eq190367 X1 x
       have i₂ := eq190380 X1 X0
       grind)
    | exact superpose eq190380 eq190367
    | exact resolve eq190367 eq190380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190380
  have eq196057 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X0) X2)) = (M.op x (M.op (M.op (M.op X0 X1) X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1506 X0 X1 X2 x
       have i₂ := eq190367 (M.op (M.op (M.op X0 X1) X0) X2) x
       grind)
    | exact superpose eq190367 eq1506
    | exact resolve eq1506 eq190367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq196083 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op X0 X1)) (M.op (M.op X0 X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6486 X0 X2 X1 (M.op X0 X1)
       have i₂ := eq190367 (M.op X0 X1) X0
       grind)
    | exact superpose eq190367 eq6486
    | exact resolve eq6486 eq190367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6486
  have eq196413 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X1)) (M.op x X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq196083 X0 X1 x
       have i₂ := eq190367 X0 x
       grind)
    | exact superpose eq190367 eq196083
    | exact resolve eq196083 eq190367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196083
  have eq196421 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op x X0) X2)) = (M.op x (M.op (M.op x X0) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq196057 X0 x X2
       have i₂ := eq190367 X0 x
       grind)
    | exact superpose eq190367 eq196057
    | exact resolve eq196057 eq190367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196057
  have eq214597 : y ≠ y ∨ y = (M.op y x) := by
    first
    | (have j0 := eq192948 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192948
  have eq214598 : y = (M.op y x) := by grind
  clear eq214597
  have eq215791 : ∀ X0 : G, x = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq190389 X0 y
       have i₂ := eq214598
       grind)
    | exact superpose eq214598 eq190389
    | exact resolve eq190389 eq214598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190389
  have eq215793 : ∀ X0 : G, (M.op x (M.op y X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq194222 y X0
       have i₂ := eq214598
       grind)
    | exact superpose eq214598 eq194222
    | exact resolve eq194222 eq214598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194222
  have eq215794 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq195231 y X0
       have i₂ := eq214598
       grind)
    | exact superpose eq214598 eq195231
    | exact resolve eq195231 eq214598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195231 eq214598
  have eq220526 : ∀ X0 X1 : G, (k (M.op y X1) y) = (M.op (M.op x X0) y) ∨ y = (M.op y (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq101809 y X0 X1
       have i₂ := eq215794 X0
       grind)
    | exact superpose eq215794 eq101809
    | (have j0 := eq101809 y X1 X1
       grind)
    | exact resolve eq101809 eq215794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101809
  have eq220726 : ∀ X1 : G, x = (k (M.op y X1) y) ∨ y = (M.op y (M.op y X1)) := by
    intro X1
    first
    | (have i₁ := eq220526 x X1
       have i₂ := eq215791 (M.op x x)
       grind)
    | exact superpose eq215791 eq220526
    | (have j0 := eq220526 x X1
       grind)
    | exact resolve eq220526 eq215791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220526
  have eq221008 : ∀ X1 : G, x = (k (M.op x X1) y) ∨ y = (M.op y (M.op y X1)) := by
    intro X1
    first
    | (have i₁ := eq220726 X1
       have i₂ := eq215794 X1
       grind)
    | exact superpose eq215794 eq220726
    | (have j0 := eq220726 X1
       grind)
    | exact resolve eq220726 eq215794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220726
  have eq221184 : ∀ X1 : G, y = (M.op x (M.op y X1)) ∨ x = (k (M.op x X1) y) := by
    intro X1
    first
    | (have i₁ := eq221008 X1
       have i₂ := eq215794 (M.op y X1)
       grind)
    | exact superpose eq215794 eq221008
    | (have j0 := eq221008 X1
       grind)
    | exact resolve eq221008 eq215794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221008
  have eq221264 : ∀ X1 : G, x = (k (M.op x X1) y) ∨ y = X1 := by
    intro X1
    first
    | (have i₁ := eq221184 X1
       have i₂ := eq215793 X1
       grind)
    | exact superpose eq215793 eq221184
    | (have j0 := eq221184 X1
       grind)
    | exact resolve eq221184 eq215793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215793 eq221184
  have eq228936 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op x (M.op (M.op (σ (k X0 X0)) X1) (M.op X1 X2))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3089 X0 X1 X2 x
       have i₂ := eq190367 (M.op (M.op (σ (k X0 X0)) X1) (M.op X1 X2)) x
       grind)
    | exact superpose eq190367 eq3089
    | (have j0 := eq3089 X0 X1 X2 x
       grind)
    | exact resolve eq3089 eq190367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089 eq190367
  have eq229431 : ∀ X0 X1 : G, (M.op (σ (k X1 X1)) X0) = (M.op x X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq228936 X1 (σ (k X1 X1)) X0
       have i₂ := eq612 X1 (σ (k X1 X1)) X0
       grind)
    | exact superpose eq612 eq228936
    | (have j0 := eq228936 X1 X1 x
       have j1 := eq612 X1 X1 x
       grind)
    | exact resolve eq228936 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612 eq228936
  have eq229696 : ∀ X0 X1 : G, (M.op (σ (k X1 X1)) X0) = (M.op x X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq229431 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229431
  have eq233133 : ∀ X0 : G, y = (M.op x X0) ∨ x = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq221264 (M.op x X0)
       have i₂ := eq194186 X0
       grind)
    | exact superpose eq194186 eq221264
    | (have j0 := eq221264 (M.op x X0)
       grind)
    | exact resolve eq221264 eq194186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq294337 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq229696 X0 y
       have i₂ := eq188963
       grind)
    | exact superpose eq188963 eq229696
    | (have j0 := eq229696 X0 y
       grind)
    | exact resolve eq229696 eq188963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229696
  have eq355750 : ∀ X0 X1 : G, (M.op x (M.op y X1)) = (M.op X0 (M.op y X1)) ∨ x = (k X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq196421 X0 x
       have i₂ := eq233133 X0
       grind)
    | exact superpose eq233133 eq196421
    | (have j1 := eq233133 X0
       grind)
    | exact resolve eq196421 eq233133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196421 eq233133
  have eq357138 : ∀ X0 X1 : G, (M.op x (M.op x X1)) = (M.op X0 (M.op x X1)) ∨ x = (k X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq355750 X0 X0
       have i₂ := eq215794 X0
       grind)
    | exact superpose eq215794 eq355750
    | (have j0 := eq355750 X0 X1
       grind)
    | exact resolve eq355750 eq215794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215794 eq355750
  have eq357332 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = X1 ∨ x = (k X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq357138 X0 X1
       have i₂ := eq194186 X1
       grind)
    | exact superpose eq194186 eq357138
    | (have j0 := eq357138 X0 X1
       grind)
    | exact resolve eq357138 eq194186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357138
  have eq357477 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op x X0) ∨ x = (k X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq357332 X1 (M.op x X0)
       have i₂ := eq194186 X0
       grind)
    | exact superpose eq194186 eq357332
    | (have j0 := eq357332 X1 X1
       grind)
    | exact resolve eq357332 eq194186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357332
  have eq360062 : ∀ X0 X1 : G, (M.op (M.op x (M.op x X0)) (M.op x X1)) = X1 ∨ x = (k X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq196413 X1 X0
       have i₂ := eq357477 X0 X1
       grind)
    | (have i₁ := eq196413 x X0
       have i₂ := eq357477 X0 X1
       grind)
    | exact superpose eq357477 eq196413
    | (have j1 := eq357477 X0 X1
       grind)
    | exact resolve eq196413 eq357477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196413 eq357477
  have eq362137 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = X1 ∨ x = (k X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq360062 X0 X1
       have i₂ := eq194186 X0
       grind)
    | exact superpose eq194186 eq360062
    | (have j0 := eq360062 X0 X1
       grind)
    | exact resolve eq360062 eq194186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194186 eq360062
  have eq368934 : ∀ X0 X1 : G, (M.op X1 (k X0 X0)) = X0 ∨ x = (k X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq165953 (M.op x X1) X1
       have i₂ := eq362137 (M.op x X1) X1
       grind)
    | exact superpose eq362137 eq165953
    | (have j1 := eq362137 X0 X0
       grind)
    | exact resolve eq165953 eq362137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362137
  have eq391111 : ∀ X0 : G, x = (k X0 y) ∨ y = (k X0 X0) ∨ x = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq221264 (k X0 X0)
       have i₂ := eq368934 X0 x
       grind)
    | exact superpose eq368934 eq221264
    | (have j0 := eq221264 (k X0 X0)
       have j1 := eq368934 X0 x
       grind)
    | exact resolve eq221264 eq368934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221264 eq368934
  have eq391146 : ∀ X0 : G, y = (k X0 X0) ∨ x = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq391111 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391111
  have eq391873 : ∀ X0 : G, (σ y) = (k X0 (σ (τ X0))) ∨ x = (k (τ X0) y) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq391146 (τ X0)
       grind)
    | exact superpose eq391146 eq17
    | (have j1 := eq391146 (τ X0)
       grind)
    | exact resolve eq17 eq391146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391146
  have eq391998 : ∀ X0 : G, x = (k (τ X0) y) ∨ (σ y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq391873 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq391873
    | (have j0 := eq391873 X0
       grind)
    | exact resolve eq391873 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391873
  have eq402522 : ∀ X0 : G, (σ x) = (k X0 (σ y)) ∨ (σ y) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq391998 X0
       grind)
    | exact superpose eq391998 eq17
    | (have j1 := eq391998 X0
       grind)
    | exact resolve eq17 eq391998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq391998
  have eq435362 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op X0 X0) (σ x)) ∨ (σ y) = (M.op X2 X2) ∨ (σ y) = (k (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138286 X1 X2 X0 (σ y)
       have i₂ := eq402522 (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq402522 eq138286
    | (have j0 := eq138286 X0 X2 X2 (σ y)
       have j1 := eq402522 (M.op X1 (M.op X2 X2))
       grind)
    | exact resolve eq138286 eq402522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138286 eq402522
  have eq435548 : ∀ X1 X2 : G, (σ y) = (M.op x (σ x)) ∨ (σ y) = (M.op X2 X2) ∨ (σ y) = (k (M.op X1 (M.op X2 X2)) (M.op X1 (M.op X2 X2))) := by
    intro X1 X2
    first
    | (have i₁ := eq435362 x X1 X2
       have i₂ := eq190371 (σ x) x
       grind)
    | exact superpose eq190371 eq435362
    | (have j0 := eq435362 x X1 X2
       grind)
    | exact resolve eq435362 eq190371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190371 eq435362
  have eq435758 : ∀ X2 : G, (σ y) = (M.op X2 X2) ∨ (σ y) = (M.op x (σ x)) ∨ (σ y) = (M.op X2 X2) := by
    intro X2
    first
    | (have i₁ := eq435548 x X2
       have i₂ := eq165125 x X2
       grind)
    | exact superpose eq165125 eq435548
    | (have j0 := eq435548 x X2
       grind)
    | exact resolve eq435548 eq165125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165125 eq435548
  have eq435759 : ∀ X2 : G, (σ y) = (M.op x (σ x)) ∨ (σ y) = (M.op X2 X2) := by
    intro X2
    first
    | (have j0 := eq435758 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435758
  have eq821793 : ∀ X0 X1 : G, (σ y) = (M.op X0 (k (σ y) (σ y))) ∨ (M.op (σ x) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq165953 (σ y) X1
       have i₂ := eq294337 X0
       grind)
    | exact superpose eq294337 eq165953
    | (have j1 := eq294337 X1
       grind)
    | exact resolve eq165953 eq294337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165953 eq294337
  have eq822133 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ (k y y))) ∨ (M.op (σ x) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq821793 X0 X1
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq821793
    | (have j0 := eq821793 X0 X1
       grind)
    | exact resolve eq821793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821793
  have eq822283 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op x X1) ∨ (σ y) = (M.op X0 (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq822133 X0 X1
       have i₂ := eq188963
       grind)
    | exact superpose eq188963 eq822133
    | (have j0 := eq822133 X0 X1
       grind)
    | exact resolve eq822133 eq188963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822133
  have eq823238 : (σ y) ≠ (M.op x (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq822283 (σ x) x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822283
  have eq823239 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq435759 (σ x)
       grind)
    | (have r₁ := eq823238
       have r₂ := eq435759 x
       grind)
    | exact resolve eq823238 eq435759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435759 eq823238
  have eq823843 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq165600 X0 (σ x)
       have i₂ := eq823239
       grind)
    | exact superpose eq823239 eq165600
    | exact resolve eq165600 eq823239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165600 eq823239
  have eq824184 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq823843 X0
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq823843
    | exact resolve eq823843 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823843
  have eq824348 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq824184 X0
       have i₂ := eq188963
       grind)
    | exact superpose eq188963 eq824184
    | exact resolve eq824184 eq188963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188963 eq824184
  have eq826960 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq824348 (σ x)
       grind)
    | exact superpose eq824348 eq16
    | exact resolve eq16 eq824348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824348
  have eq827243 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq826960
       have i₂ := eq215791 x
       grind)
    | exact superpose eq215791 eq826960
    | exact resolve eq826960 eq215791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215791 eq826960
  have eq827244 : False := by grind
  exact eq827244

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyy_pyx_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  clear eq36
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
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
  clear eq44
  have eq85 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq78
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79
    | exact resolve eq79 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq87
    | exact resolve eq87 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq96 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq70
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq70 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq96
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq146 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq129
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq129
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq129 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq146
  have eq167 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq189 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq204 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF1
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ (M.op x y))
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq206 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X1 X2)) = (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X1 X2) X3 X1
       have i₂ := eq53 X1 X0 X2
       grind)
    | (have i₁ := eq53 (M.op X1 X1) X1 X0
       have i₂ := eq53 X0 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 X1 X3 x
       have i₂ := eq53 X1 X0 x
       grind)
    | (have i₁ := eq53 X0 X1 X0
       have i₂ := eq53 X0 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X0) x X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq50 eq53
    | exact resolve eq53 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq354 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 x X2
       have i₂ := eq53 X0 x X1
       grind)
    | (have i₁ := eq53 X2 X2 X2
       have i₂ := eq53 X2 X1 X2
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 x
       have i₂ := eq53 X1 X0 x
       grind)
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq53 X0 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op (M.op x y) x) X0)) = (M.op x (M.op (M.op (M.op x y) x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq353 eq53
    | exact resolve eq53 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq833 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq354 sF4
       have i₂ := eq53 sF4 x sF2
       grind)
    | exact superpose eq53 eq354
    | exact resolve eq354 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq843 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq354 eq53
    | exact resolve eq53 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq342 X3 X1 x
       have i₂ := eq342 X0 X1 x
       grind)
    | (have i₁ := eq342 X0 X1 X3
       have i₂ := eq342 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq342 eq342
    | exact resolve eq342 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq342 X0 (M.op X1 X1) X3
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq342 X0 (M.op X1 X1) X3
       have i₂ := eq342 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq342 eq342
    | exact resolve eq342 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1112 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq51
    | exact resolve eq51 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1117 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X0 (M.op X1 X1)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq206 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq206 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq206
    | exact resolve eq206 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1118 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 (M.op X1 X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq209 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq209 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq209
    | exact resolve eq209 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1083 X0 X1 x X3
       have i₂ := eq52 X0 x X1
       grind)
    | exact superpose eq52 eq1083
    | exact resolve eq1083 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1083
  have eq1185 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq833 eq53
    | exact resolve eq53 eq833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq833
  have eq1189 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1185 X0 x
       have i₂ := eq357 X0 sF4 x
       grind)
    | exact superpose eq357 eq1185
    | exact resolve eq1185 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1192 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (M.op X1 X1)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1189 (M.op X1 X1)
       have i₂ := eq342 X0 X1 X1
       grind)
    | (have i₁ := eq1189 (M.op X1 X1)
       have i₂ := eq342 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq342 eq1189
    | exact resolve eq1189 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq2866 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq352 X0 X1 (M.op X0 X1)
       have i₂ := eq356 (M.op X0 X1) X2 X0
       grind)
    | (have i₁ := eq352 X0 X1 (M.op X0 X1)
       have i₂ := eq356 (M.op X0 X1) X0 X2
       grind)
    | exact superpose eq356 eq352
    | exact resolve eq352 eq356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq356
  have eq3388 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq354 eq345
    | exact resolve eq345 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq354
  have eq3605 : ∀ X1 X2 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op X2 X2) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) (σ x)) := by
    intro X1 X2
    first
    | exact superpose eq209 eq3388
    | exact resolve eq3388 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq3388
  have eq4552 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq167 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq167
    | (have j0 := eq167 x
       grind)
    | exact resolve eq167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq4563 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4552
  have eq4567 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4563
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4563
    | exact resolve eq4563 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4563
  have eq4583 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4567
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq4567 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4567
  have eq4589 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4583 eq49
    | exact resolve eq49 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq4775 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq189 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq189
    | (have j0 := eq189 y
       grind)
    | exact resolve eq189 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq4785 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4775
  have eq4788 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4785
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq4785
    | exact resolve eq4785 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4785
  have eq4810 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4788
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq4788 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4788
  have eq4824 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4810 eq101
    | exact resolve eq101 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq5015 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq204
    | (have j0 := eq204 (M.op x y)
       grind)
    | exact resolve eq204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq5024 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq5015
  have eq5026 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq129 eq5024
    | exact resolve eq5024 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5024
  have eq5052 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq5026
       have r₂ := eq13 x (σ (M.op x y))
       grind)
    | exact resolve eq5026 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5026
  have eq5070 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5052 eq152
    | exact resolve eq152 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq11880 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4583 eq85
    | exact resolve eq85 eq4583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq4583
  have eq12200 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4810 eq102
    | exact resolve eq102 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq13453 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5052 eq153
    | exact resolve eq153 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq17029 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq11880
       grind)
    | exact superpose eq11880 eq16
    | exact resolve eq16 eq11880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11880
  have eq17080 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4589 eq17029
    | exact resolve eq17029 eq4589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17029
  have eq17083 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq17080
       have r₂ := eq13 x x
       grind)
    | exact resolve eq17080 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17080
  have eq17662 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq12200
       grind)
    | exact superpose eq12200 eq16
    | exact resolve eq16 eq12200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12200
  have eq17717 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4824 eq17662
    | exact resolve eq17662 eq4824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17662
  have eq17720 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq17717
       have r₂ := eq13 x y
       grind)
    | exact resolve eq17717 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17717
  have eq17721 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq17720
       grind)
    | exact superpose eq17720 eq70
    | exact resolve eq70 eq17720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq17754 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq4810 eq17721
    | exact resolve eq17721 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810 eq17721
  have eq18584 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq13453 eq16
    | exact resolve eq16 eq13453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13453
  have eq18643 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5070 eq18584
    | exact resolve eq18584 eq5070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5070 eq18584
  have eq18646 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq18643
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq18643 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18643
  have eq18647 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq18646 eq129
    | exact resolve eq129 eq18646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq18646
  have eq18680 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq5052 eq18647
    | exact resolve eq18647 eq5052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5052 eq18647
  have eq24095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq24096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq24095
    | exact resolve eq24095 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24095
  have eq24107 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq24096
       have r₂ := eq27
       grind)
    | exact resolve eq24096 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24096
  have eq24111 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq24107 eq4824
    | exact resolve eq4824 eq24107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24107
  have eq24193 : (τ (σ y)) = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq24111
       have i₂ := eq17720
       grind)
    | exact superpose eq17720 eq24111
    | exact resolve eq24111 eq17720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24111
  have eq24202 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq24193
    | exact resolve eq24193 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24193
  have eq24203 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq24202
  have eq24207 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq24203 eq14
    | exact resolve eq14 eq24203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24306 : (σ x) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24207 eq1112
    | exact resolve eq1112 eq24207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq24309 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24207 eq1118
    | exact resolve eq1118 eq24207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq24352 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq24207 eq1072
    | exact resolve eq1072 eq24207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24207
  have eq24616 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24309 eq24306
    | exact resolve eq24306 eq24309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24306 eq24309
  have eq24631 : (σ x) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq24616
  have eq25472 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq24352
    | (have j0 := eq24352 (σ x) X0
       grind)
    | exact resolve eq24352 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24352
  have eq26971 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24203 eq24631
    | exact resolve eq24631 eq24203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24203 eq24631
  have eq26986 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq26971
  have eq27010 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26986 eq25472
    | exact resolve eq25472 eq26986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25472 eq26986
  have eq27082 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq27010
  have eq27127 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq17754
       have i₂ := eq27082
       grind)
    | exact superpose eq27082 eq17754
    | exact resolve eq17754 eq27082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27162 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq1072 X0 y x
       have i₂ := eq27082
       grind)
    | exact superpose eq27082 eq1072
    | exact resolve eq1072 eq27082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27082
  have eq27201 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq27127
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27127
    | exact resolve eq27127 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27127
  have eq27445 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq27201 eq1072
    | exact resolve eq1072 eq27201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27201
  have eq29196 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq27162 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27162
    | (have j0 := eq27162 x X0
       grind)
    | exact resolve eq27162 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27162
  have eq29845 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq17754
       have i₂ := eq29196 y
       grind)
    | exact superpose eq29196 eq17754
    | exact resolve eq17754 eq29196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29196
  have eq29875 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq29845
    | exact resolve eq29845 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29845
  have eq32586 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq27445
    | (have j0 := eq27445 (σ x) X0
       grind)
    | exact resolve eq27445 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27445
  have eq33117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32586 eq29875
    | exact resolve eq29875 eq32586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29875 eq32586
  have eq33120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq33117
  have eq33150 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq33120
       have r₂ := eq27
       grind)
    | exact resolve eq33120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33120
  have eq33450 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq33150
       grind)
    | exact superpose eq33150 eq14
    | exact resolve eq14 eq33150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33150
  have eq33929 : ∀ X0 : G, y = (M.op X0 (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq33450 x
       have i₂ := eq342 X0 y x
       grind)
    | (have i₁ := eq33450 X0
       have i₂ := eq342 (M.op X0 X0) y x
       grind)
    | exact superpose eq342 eq33450
    | exact resolve eq33450 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq34030 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1072 X0 (M.op y y) x
       have i₂ := eq33450 y
       grind)
    | exact superpose eq33450 eq1072
    | exact resolve eq1072 eq33450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33450
  have eq34658 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq34030 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq34030
    | (have j0 := eq34030 x X0
       grind)
    | exact resolve eq34030 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34030
  have eq35146 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17754
       have i₂ := eq34658 y
       grind)
    | exact superpose eq34658 eq17754
    | exact resolve eq17754 eq34658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17754
  have eq35157 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq33929 X0
       have i₂ := eq34658 y
       grind)
    | exact superpose eq34658 eq33929
    | exact resolve eq33929 eq34658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33929 eq34658
  have eq35166 : ∀ X0 : G, y = (M.op X0 (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq35157 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35157
  have eq35186 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq35146
    | exact resolve eq35146 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35146
  have eq35581 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35166 eq18680
    | exact resolve eq18680 eq35166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18680 eq35166
  have eq35601 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35581
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35581
    | exact resolve eq35581 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq35581
  have eq35931 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op X0 (M.op X1 (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq35186 eq1168
    | exact resolve eq1168 eq35186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35186
  have eq43100 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq35601 eq35931
    | exact resolve eq35931 eq35601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35601 eq35931
  have eq43317 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq43100 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43100
  have eq43500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq43317 eq26
    | (have j1 := eq43317 (σ x)
       grind)
    | exact resolve eq26 eq43317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43317
  have eq43545 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq43500
       have r₂ := eq27
       grind)
    | exact resolve eq43500 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43500
  have eq43559 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq43545 eq27
    | exact resolve eq27 eq43545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq43573 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ x)) X1)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq43545 eq3605
    | exact resolve eq3605 eq43545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3605
  have eq43583 : ∀ X1 : G, (M.op (σ x) (σ x)) = (M.op X1 (σ x)) := by
    intro X1
    first
    | (have i₁ := eq43573 x X1
       have i₂ := eq357 sF2 X1 x
       grind)
    | exact superpose eq357 eq43573
    | exact resolve eq43573 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43573
  have eq44177 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op X0 (M.op x (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)))) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq830 eq1192
    | exact resolve eq1192 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq1192
  have eq44225 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (M.op x (M.op (M.op (M.op x y) x) (M.op (M.op x y) x)))) (σ x))) := by
    intro X0
    first
    | exact superpose eq43545 eq44177
    | exact resolve eq44177 eq43545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44177
  have eq44270 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq43583 eq44225
    | exact resolve eq44225 eq43583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44225
  have eq44286 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq44270
       have i₂ := eq1072 sF2 sF2 x
       grind)
    | (have i₁ := eq44270
       have i₂ := eq1072 X0 sF2 sF2
       grind)
    | exact superpose eq1072 eq44270
    | exact resolve eq44270 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44270
  have eq44443 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X1 (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq44286 eq1072
    | exact resolve eq1072 eq44286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq44931 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = (M.op (M.op X1 X1) (M.op (M.op (σ x) (σ x)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq43583 eq843
    | exact resolve eq843 eq43583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq43583
  have eq44932 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ x)) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq44931 x x
       have i₂ := eq357 sF2 x x
       grind)
    | exact superpose eq357 eq44931
    | exact resolve eq44931 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq44931
  have eq45034 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44932 X1
       have i₂ := eq350 sF2 X1 x
       grind)
    | (have i₁ := eq44932 X1
       have i₂ := eq350 X0 X1 sF2
       grind)
    | exact superpose eq350 eq44932
    | exact resolve eq44932 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq44932
  have eq45602 : ∀ X0 : G, (k x x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq44443 eq4589
    | exact resolve eq4589 eq44443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4589 eq44443
  have eq45666 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq45602 X0
       have i₂ := eq17083
       grind)
    | exact superpose eq17083 eq45602
    | exact resolve eq45602 eq17083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17083 eq45602
  have eq47160 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq44286 eq45034
    | exact resolve eq45034 eq44286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45034
  have eq48277 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq47160
    | (have j0 := eq47160 (σ y)
       grind)
    | exact resolve eq47160 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq47160
  have eq48381 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq43545 eq48277
    | exact resolve eq48277 eq43545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43545 eq48277
  have eq48414 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq48381 eq44286
    | exact resolve eq44286 eq48381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44286
  have eq48421 : (τ (σ y)) = (M.op x x) := by
    first
    | exact superpose eq48381 eq45666
    | exact resolve eq45666 eq48381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45666 eq48381
  have eq48533 : y = (M.op x x) := by
    first
    | exact superpose eq29 eq48421
    | exact resolve eq48421 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq48421
  have eq49058 : (τ (σ x)) = (k y y) := by
    first
    | exact superpose eq48414 eq4824
    | exact resolve eq4824 eq48414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4824 eq48414
  have eq49090 : (τ (σ x)) = (M.op y y) := by
    first
    | (have i₁ := eq49058
       have i₂ := eq17720
       grind)
    | exact superpose eq17720 eq49058
    | exact resolve eq49058 eq17720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17720 eq49058
  have eq49128 : x = (M.op y y) := by
    first
    | exact superpose eq28 eq49090
    | exact resolve eq49090 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq49090
  have eq49330 : (M.op (M.op x y) x) = (M.op x x) := by
    first
    | (have i₁ := eq206 y
       have i₂ := eq49128
       grind)
    | exact superpose eq49128 eq206
    | exact resolve eq206 eq49128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq49447 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq49330
       have i₂ := eq48533
       grind)
    | exact superpose eq48533 eq49330
    | exact resolve eq49330 eq48533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48533 eq49330
  have eq50316 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op x (M.op X0 X0)) X1) (M.op x (M.op X0 X0))) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2866 x (M.op X0 X0) X1
       have i₂ := eq1117 x X0
       grind)
    | exact superpose eq1117 eq2866
    | exact resolve eq2866 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117 eq2866
  have eq50455 : ∀ X0 X1 : G, x = (M.op (M.op (M.op (M.op x (M.op X0 X0)) X1) (M.op x (M.op X0 X0))) y) := by
    intro X0 X1
    first
    | exact superpose eq49447 eq50316
    | exact resolve eq50316 eq49447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49447 eq50316
  have eq50570 : ∀ X0 : G, x = (M.op (M.op X0 X0) y) := by
    intro X0
    first
    | (have i₁ := eq50455 X0 x
       have i₂ := eq1168 x X0 (M.op (M.op x (M.op X0 X0)) x)
       grind)
    | exact superpose eq1168 eq50455
    | exact resolve eq50455 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq50455
  have eq50750 : x = (M.op x y) := by
    first
    | (have i₁ := eq50570 y
       have i₂ := eq49128
       grind)
    | exact superpose eq49128 eq50570
    | exact resolve eq50570 eq49128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49128 eq50570
  have eq50872 : x = (M.op x y) := by
    first
    | (have i₁ := eq50750
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50750
    | exact resolve eq50750 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq50750
  have eq50886 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq50872 eq20
    | exact resolve eq20 eq50872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq50872
  have eq51098 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq50886
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50886
    | exact resolve eq50886 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq50886
  have eq51151 : False := by grind
  exact eq51151

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxy_pxx_pxy_Equation1724 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
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
  have eq53 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op (M.op x y) x)) := by
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
  have eq54 : ∀ X0 : G, (σ x) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) X1 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X2) X0) X1 (M.op (M.op X0 X2) X0)
       have i₂ := eq14 X0 (M.op (M.op X0 X2) X0) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq49
       grind)
    | exact superpose eq49 eq16
    | exact resolve eq16 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq72
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq72
    | exact resolve eq72 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq85 : x ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op x x) := by
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
  have eq86 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 X0) x) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op X0 X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq241 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq230 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq230
    | exact resolve eq230 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq242 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq241
  have eq375 : ∀ X0 : G, (σ x) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq54
    | exact resolve eq54 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq214 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq214
    | exact resolve eq214 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq494 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X3) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq56 (M.op X1 X1) X3 (M.op (M.op X0 x) X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (M.op (M.op X0 X1) X0) x X2
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) x) X0) (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq214 eq56
    | exact resolve eq56 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq214
  have eq650 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq242 X0
       grind)
    | exact superpose eq242 eq16
    | exact resolve eq16 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq869 : ∀ X0 : G, x = (M.op (τ (M.op X0 X0)) (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq53 (τ X0)
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq53
    | exact resolve eq53 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq874 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (τ (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq211 (τ X0)
       have i₂ := eq650 X0
       grind)
    | exact superpose eq650 eq211
    | exact resolve eq211 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq1263 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1263
    | exact resolve eq1263 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1267 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1264
       have r₂ := eq28
       grind)
    | exact resolve eq1264 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1269 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1267
    | exact resolve eq1267 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1273 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1269 eq86
    | (have r₁ := eq86
       have r₂ := eq1269
       grind)
    | exact resolve eq86 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1277 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1273
  have eq1278 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1277
  have eq1346 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1278 eq77
    | exact resolve eq77 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1347 : (k x y) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1278 eq60
    | exact resolve eq60 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq1278
  have eq1350 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1346
  have eq1354 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq68 eq1347
    | exact resolve eq1347 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347
  have eq1357 : (k x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1354
       have r₂ := eq85
       grind)
    | exact resolve eq1354 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq1354
  have eq1465 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1357
       grind)
    | exact superpose eq1357 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1466 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1465
  have eq1468 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1466
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1466
    | exact resolve eq1466 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1471 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1468
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1468
    | exact resolve eq1468 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1488 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1350 eq516
    | exact resolve eq516 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq1489 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq1350 eq14
    | exact resolve eq14 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1491 : (σ x) = (M.op (σ (M.op x y)) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1350 eq54
    | exact resolve eq54 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1498 : (σ x) = (M.op (σ (σ (M.op x y))) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1350 eq375
    | exact resolve eq375 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1570 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq494 X3 X1 x
       have i₂ := eq494 X0 X1 x
       grind)
    | (have i₁ := eq494 X0 X1 X3
       have i₂ := eq494 (M.op X3 X3) X1 X3
       grind)
    | exact superpose eq494 eq494
    | exact resolve eq494 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1582 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X1))) = (M.op (M.op X2 X2) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq494 X0 (M.op X1 X1) X3
       have i₂ := eq494 X0 X1 X1
       grind)
    | (have i₁ := eq494 X0 (M.op X1 X1) X3
       have i₂ := eq494 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq494 eq494
    | exact resolve eq494 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1615 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op (M.op X2 X3) X2)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) X3
       have i₂ := eq494 X0 X1 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X1) X2
       have i₂ := eq494 (M.op X1 X1) X1 X3
       grind)
    | exact superpose eq494 eq14
    | exact resolve eq14 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1624 : ∀ X0 X1 : G, (σ x) = (M.op (σ (M.op X0 (M.op X1 X1))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq375 (M.op X1 X1)
       have i₂ := eq494 X0 X1 X1
       grind)
    | (have i₁ := eq375 (M.op X1 X1)
       have i₂ := eq494 (M.op X1 X1) X1 x
       grind)
    | exact superpose eq494 eq375
    | exact resolve eq375 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq494
  have eq1693 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1582 X0 X1 x X3
       have i₂ := eq55 X0 x X1
       grind)
    | exact superpose eq55 eq1582
    | exact resolve eq1582 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1582
  have eq1775 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1269 eq1488
    | exact resolve eq1488 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1786 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1775
  have eq1795 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1488 eq1491
    | exact resolve eq1491 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488 eq1491
  have eq1803 : (σ x) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1795
  have eq2044 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1786 eq1350
    | exact resolve eq1350 eq1786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq1786
  have eq2077 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2044
  have eq2143 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2077 eq1803
    | exact resolve eq1803 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq2151 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2143
  have eq2174 : x = (M.op (τ (σ x)) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2151 eq869
    | exact resolve eq869 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq2176 : (M.op (M.op x y) x) = (M.op (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2151 eq874
    | exact resolve eq874 eq2151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq2151
  have eq2184 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq2176
    | exact resolve eq2176 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176
  have eq2186 : x = (M.op x (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq2174
    | exact resolve eq2174 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174
  have eq3199 : x = (M.op x (M.op x x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2184 eq2186
    | exact resolve eq2186 eq2184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184 eq2186
  have eq3209 : x = (M.op x (M.op x x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq3199
  have eq3768 : (M.op x y) = (M.op x (M.op (M.op (M.op x y) x) (M.op x y))) := by
    first
    | exact superpose eq513 eq512
    | exact resolve eq512 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq513
  have eq5308 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3209
       have i₂ := eq1471
       grind)
    | exact superpose eq1471 eq3209
    | exact resolve eq3209 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471 eq3209
  have eq5324 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq5308
  have eq12060 : (σ x) = (M.op (σ (σ (M.op x y))) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1269 eq1498
    | exact resolve eq1498 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq12096 : (σ x) = (M.op (σ (σ (M.op x y))) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12060
  have eq12875 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq12096 eq1570
    | exact resolve eq1570 eq12096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12096
  have eq24106 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4, g5, g6⟩ := hcon
    have f24106_18 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op (M.op X0 X1) X0)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
      intro X0 X1
      grind
    have f24106_19 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
      intro X0
      grind
    have f24106_28 : X0 ≠ (M.op (σ (M.op x y)) (M.op (σ x) X0)) := by grind
    have f24106_32 : x ≠ (M.op x y) := by grind
    have f24106_33 : x ≠ y := by grind
    have f24106_34 : (σ x) ≠ (σ y) := by grind
    have f24106_36 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ x = y ∨ (σ x) = (σ y) := by
      intro X0
      first
      | (have j0 := f24106_19 X0
         grind)
      | (have r₁ := f24106_19 X0
         have r₂ := f24106_32
         grind)
      | exact resolve f24106_19 f24106_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24106_37 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op (M.op X0 X1) X0)) = X0 ∨ x = y ∨ (σ x) = (σ y) := by
      intro X0 X1
      first
      | (have j0 := f24106_18 X0 X1
         grind)
      | (have r₁ := f24106_18 X0 X1
         have r₂ := f24106_32
         grind)
      | exact resolve f24106_18 f24106_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24106_38 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) := by
      intro X0
      first
      | (have j0 := f24106_36 X0
         grind)
      | (have r₁ := f24106_36 X0
         have r₂ := f24106_33
         grind)
      | exact resolve f24106_36 f24106_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24106_39 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op (M.op X0 X1) X0)) = X0 ∨ (σ x) = (σ y) := by
      intro X0 X1
      first
      | (have j0 := f24106_37 X0 X1
         grind)
      | (have r₁ := f24106_37 X0 X1
         have r₂ := f24106_33
         grind)
      | exact resolve f24106_37 f24106_33
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24106_40 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ x))) := by
      intro X0
      first
      | (have j0 := f24106_38 X0
         grind)
      | (have r₁ := f24106_38 X0
         have r₂ := f24106_34
         grind)
      | exact resolve f24106_38 f24106_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24106_41 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (M.op (M.op X0 X1) X0)) = X0 := by
      intro X0 X1
      first
      | (have j0 := f24106_39 X0 X1
         grind)
      | (have r₁ := f24106_39 X0 X1
         have r₂ := f24106_34
         grind)
      | exact resolve f24106_39 f24106_34
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24106_72 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ x) X0)) = X0 := by
      intro X0
      first
      | (have i₁ := f24106_41 X0 (M.op (σ x) (σ x))
         have i₂ := f24106_40 X0
         grind)
      | exact superpose f24106_40 f24106_41
      | exact resolve f24106_41 f24106_40
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24106_344 : X0 ≠ X0 := by
      first
      | (have i₁ := f24106_28
         have i₂ := f24106_72 X0
         grind)
      | exact superpose f24106_72 f24106_28
      | (have r₁ := f24106_28
         have r₂ := f24106_72 X0
         grind)
      | exact resolve f24106_28 f24106_72
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f24106_350 : False := by grind
    exact f24106_350
  clear eq1489 eq12875
  have eq24565 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ x) X0)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq24106 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24106
  have eq24817 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq24565
    | (have j0 := eq24565 (σ y)
       grind)
    | exact resolve eq24565 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24565
  have eq24921 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1269 eq24817
    | exact resolve eq24817 eq1269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269 eq24817
  have eq24950 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq24921
  have eq24981 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq24950 eq2077
    | exact resolve eq2077 eq24950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077 eq24950
  have eq25036 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq24981
  have eq25056 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq25036 eq30
    | exact resolve eq30 eq25036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25036
  have eq25097 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq25056
    | exact resolve eq25056 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25056
  have eq25098 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq25097
  have eq25108 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25098 eq30
    | exact resolve eq30 eq25098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25098
  have eq25165 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq25108
    | exact resolve eq25108 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq25108
  have eq25266 : x = (M.op x y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq25165 eq5324
    | exact resolve eq5324 eq25165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5324 eq25165
  have eq25304 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq25266
  have eq25338 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25304
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq25304
    | exact resolve eq25304 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25304
  have eq25339 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq25338
  have eq25408 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq25339 eq30
    | exact resolve eq30 eq25339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq25339
  have eq25451 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq25408
    | exact resolve eq25408 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25408
  have eq25452 : x = (M.op x y) ∨ x = y := by grind
  clear eq25451
  have eq25461 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq25452 eq21
    | exact resolve eq21 eq25452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25525 : x = (M.op x (M.op (M.op x x) x)) ∨ x = y := by
    first
    | exact superpose eq25452 eq3768
    | exact resolve eq3768 eq25452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3768
  have eq25532 : x = (M.op x (M.op (M.op x y) x)) ∨ x = y := by
    first
    | (have i₁ := eq25525
       have i₂ := eq211 x
       grind)
    | exact superpose eq211 eq25525
    | exact resolve eq25525 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq25525
  have eq25585 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq25461
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25461
    | exact resolve eq25461 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25461
  have eq25902 : x = (M.op x (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq25452 eq25532
    | exact resolve eq25532 eq25452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25532
  have eq25932 : x = (M.op x (M.op x x)) ∨ x = y := by grind
  clear eq25902
  have eq26703 : ∀ X0 : G, x = (M.op X0 (M.op x x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq25932
       have i₂ := eq1570 x x X0
       grind)
    | (have i₁ := eq25932
       have i₂ := eq1570 X0 x x
       grind)
    | exact superpose eq1570 eq25932
    | exact resolve eq25932 eq1570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq26715 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq1624 x x
       have i₂ := eq25932
       grind)
    | exact superpose eq25932 eq1624
    | exact resolve eq1624 eq25932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624
  have eq26717 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1693 x x X0
       have i₂ := eq25932
       grind)
    | exact superpose eq25932 eq1693
    | exact resolve eq1693 eq25932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693
  have eq26745 : (σ x) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq26715
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26715
    | exact resolve eq26715 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26715
  have eq27494 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq383 (M.op x x)
       have i₂ := eq26703 (M.op x x)
       grind)
    | exact superpose eq26703 eq383
    | exact resolve eq383 eq26703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq27636 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq27494
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27494
    | exact resolve eq27494 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27494
  have eq27986 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq52
       have i₂ := eq26717 X0
       grind)
    | (have i₁ := eq52
       have i₂ := eq26717 x
       grind)
    | exact superpose eq26717 eq52
    | exact resolve eq52 eq26717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq26717
  have eq29661 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq27636 eq26745
    | exact resolve eq26745 eq27636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26745 eq27636
  have eq29703 : (σ x) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = y := by grind
  clear eq29661
  have eq35487 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq1615 x x X0 X1
       have i₂ := eq25932
       grind)
    | exact superpose eq25932 eq1615
    | exact resolve eq1615 eq25932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615 eq25932
  have eq55094 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 ∨ x = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq35487 X0 (M.op x x)
       have i₂ := eq26703 X0
       grind)
    | exact superpose eq26703 eq35487
    | exact resolve eq35487 eq26703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26703 eq35487
  have eq55807 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq55094 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55094
  have eq55861 : y = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq55807 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55807
    | (have j0 := eq55807 y
       grind)
    | exact resolve eq55807 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55807
  have eq56068 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq25452 eq55861
    | exact resolve eq55861 eq25452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25452 eq55861
  have eq56112 : y = (M.op x x) ∨ x = y := by grind
  clear eq56068
  have eq56160 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq27986 x
       have i₂ := eq56112
       grind)
    | exact superpose eq56112 eq27986
    | exact resolve eq27986 eq56112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27986 eq56112
  have eq56266 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq56160
  have eq56322 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq56266
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq56266
    | exact resolve eq56266 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56266
  have eq57029 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq56322 eq29703
    | exact resolve eq29703 eq56322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29703 eq56322
  have eq57198 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq57029
  have eq57240 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq57198
    | exact resolve eq57198 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57198
  have eq57244 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq57240 eq28
    | exact resolve eq28 eq57240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57240
  have eq57312 : x = y := by
    first
    | (have r₁ := eq57244
       have r₂ := eq25585
       grind)
    | exact resolve eq57244 eq25585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25585 eq57244
  have eq57313 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq57312
       grind)
    | exact superpose eq57312 eq19
    | exact resolve eq19 eq57312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq57314 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq57312
       grind)
    | exact superpose eq57312 eq25
    | exact resolve eq25 eq57312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq57312
  have eq57435 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq57314
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57314
    | exact resolve eq57314 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq57314
  have eq57455 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq57435 eq27
    | exact resolve eq27 eq57435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq57435
  have eq57745 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq57455 eq68
    | exact resolve eq68 eq57455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq57455
  have eq57894 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq57745
       have i₂ := eq57313
       grind)
    | exact superpose eq57313 eq57745
    | exact resolve eq57745 eq57313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57313 eq57745
  have eq57902 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq57894 eq15
    | exact resolve eq15 eq57894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57894
  have eq57986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq57902
    | exact resolve eq57902 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq57902
  have eq58007 : False := by grind
  exact eq58007

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pxy_Equation1728 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq72 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq33
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = X1 := by
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
  clear eq18
  have eq86 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq89 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq54 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq90 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq197 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq372 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq402 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq372
    | (have j0 := eq372 X0 X1
       grind)
    | exact resolve eq372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq753 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq197
       have i₂ := eq402 x y
       grind)
    | exact superpose eq402 eq197
    | (have j1 := eq402 (σ x) (σ y)
       grind)
    | (have r₁ := eq197
       have r₂ := eq402 x y
       grind)
    | (have r₁ := eq197
       have r₂ := eq402 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq197
       have r₂ := eq402 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq197 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq402
  have eq754 : x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq753
  have eq766 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq12
    | (have j0 := eq12 X1 (τ X0)
       have j1 := eq72 X0
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq72 X0
       grind)
    | exact resolve eq12 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq771 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq766 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq2403 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq771 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq771
    | exact resolve eq771 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq2485 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2403 X0 X1
       have i₂ := eq24 (σ X0) X0
       grind)
    | exact superpose eq24 eq2403
    | (have j0 := eq2403 X0 X1
       grind)
    | exact resolve eq2403 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2403
  have eq2496 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2485 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2485
    | (have j0 := eq2485 X0 X0
       grind)
    | exact resolve eq2485 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485
  have eq2711 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2496 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2496
  have eq2712 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2711 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2768 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq2712 X0
       grind)
    | exact superpose eq2712 eq89
    | (have j0 := eq89 X0
       grind)
    | exact resolve eq89 eq2712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq2769 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq2712 X0
       grind)
    | exact superpose eq2712 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq2712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq2794 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2712 (σ X0)
       grind)
    | exact superpose eq2712 eq15
    | exact resolve eq15 eq2712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2828 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2794 X0
       have i₂ := eq2712 X0
       grind)
    | exact superpose eq2712 eq2794
    | exact resolve eq2794 eq2712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2712 eq2794
  have eq24791 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq754
       grind)
    | exact superpose eq754 eq16
    | exact resolve eq16 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq24792 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq24791
       have r₂ := eq2828 x
       grind)
    | exact resolve eq24791 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24791
  have eq24793 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq24792
       have i₂ := eq2828 y
       grind)
    | exact superpose eq2828 eq24792
    | exact resolve eq24792 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24792
  have eq25142 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24793
       grind)
    | exact superpose eq24793 eq10
    | exact resolve eq10 eq24793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24793
  have eq25247 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq25142
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25142
    | exact resolve eq25142 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25142
  have eq25275 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25247
       grind)
    | exact superpose eq25247 eq16
    | exact resolve eq16 eq25247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25247
  have eq25276 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq25275
       have r₂ := eq2828 x
       grind)
    | exact resolve eq25275 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25275
  have eq25632 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2768 y
       have i₂ := eq25276
       grind)
    | exact superpose eq25276 eq2768
    | (have j0 := eq2768 y
       grind)
    | (have r₁ := eq2768 y
       have r₂ := eq25276
       grind)
    | exact resolve eq2768 eq25276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25633 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq2769 y X0
       have i₂ := eq25276
       grind)
    | exact superpose eq25276 eq2769
    | (have j0 := eq2769 y X0
       grind)
    | (have r₁ := eq2769 y x
       have r₂ := eq25276
       grind)
    | exact resolve eq2769 eq25276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25276
  have eq25665 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq25633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25633
  have eq25666 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq25632
  have eq25676 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq25665 X0
       have j1 := eq2769 y X0
       grind)
    | (have r₁ := eq25665 X0
       have r₂ := eq2769 y x
       grind)
    | exact resolve eq25665 eq2769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769 eq25665
  have eq25677 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq2768 y
       grind)
    | (have r₁ := eq25666
       have r₂ := eq2768 y
       grind)
    | exact resolve eq25666 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768 eq25666
  have eq25681 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq25677
       have i₂ := eq2828 y
       grind)
    | exact superpose eq2828 eq25677
    | exact resolve eq25677 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828 eq25677
  have eq25696 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq25681
       grind)
    | exact superpose eq25681 eq10
    | exact resolve eq10 eq25681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25681
  have eq25805 : y = (M.op y y) := by
    first
    | (have i₁ := eq25696
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq25696
    | exact resolve eq25696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25696
  have eq26197 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq25805
       grind)
    | exact superpose eq25805 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq25805
       grind)
    | exact resolve eq12 eq25805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25805
  have eq26246 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq26197 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26197
  have eq26820 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq25676 (σ X0)
       grind)
    | exact superpose eq25676 eq15
    | exact resolve eq15 eq25676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25676
  have eq26902 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq26820 X0
       have i₂ := eq26246 X0
       grind)
    | exact superpose eq26246 eq26820
    | exact resolve eq26820 eq26246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26246 eq26820
  have eq27751 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26902 x
       grind)
    | exact superpose eq26902 eq16
    | (have r₁ := eq16
       have r₂ := eq26902 x
       grind)
    | exact resolve eq16 eq26902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26902
  have eq27832 : False := by grind
  exact eq27832

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1728 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq545 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq548 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3445 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq545 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq545
    | exact resolve eq545 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq3490 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3445 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3445
    | (have j0 := eq3445 X0 X1
       grind)
    | exact resolve eq3445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3445
  have eq3631 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq548 x y
       grind)
    | exact superpose eq548 eq16
    | (have j1 := eq548 x y
       grind)
    | exact resolve eq16 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3641 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq548 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq6650 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3631
       have i₂ := eq3490 y x
       grind)
    | exact superpose eq3490 eq3631
    | (have j1 := eq3490 (σ y) (σ x)
       grind)
    | (have r₁ := eq3631
       have r₂ := eq3490 y x
       grind)
    | (have r₁ := eq3631
       have r₂ := eq3490 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3631
       have r₂ := eq3490 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3631 eq3490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6651 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq6650
  have eq17935 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) ≠ (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3641 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3641
    | exact resolve eq3641 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3641
  have eq17958 : ∀ X0 X1 : G, (k X0 (σ X1)) ≠ (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17935 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq17935
    | (have j0 := eq17935 X0 X1
       grind)
    | exact resolve eq17935 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17935
  have eq17971 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17958 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17958
    | exact resolve eq17958 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17958
  have eq19945 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6651
       grind)
    | exact superpose eq6651 eq16
    | exact resolve eq16 eq6651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6651
  have eq19946 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq19945
       have r₂ := eq22 x
       grind)
    | exact resolve eq19945 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19945
  have eq19949 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19946
       grind)
    | exact superpose eq19946 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19946
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19946
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19946
       grind)
    | exact resolve eq13 eq19946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19946
  have eq19953 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq19949
  have eq20225 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19953
       grind)
    | exact superpose eq19953 eq16
    | exact resolve eq16 eq19953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19953
  have eq20226 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq20225
       have r₂ := eq22 x
       grind)
    | exact resolve eq20225 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20225
  have eq20231 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq20226
       grind)
    | exact superpose eq20226 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20226
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20226
       grind)
    | exact resolve eq13 eq20226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20226
  have eq20238 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq20231
  have eq20239 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by grind
  clear eq20238
  have eq20245 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq20239
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq20239
    | exact resolve eq20239 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20239
  have eq20297 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20245
       grind)
    | exact superpose eq20245 eq16
    | exact resolve eq16 eq20245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20245
  have eq20338 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq20297
       have i₂ := eq3490 y x
       grind)
    | exact superpose eq3490 eq20297
    | (have j1 := eq3490 y x
       grind)
    | (have r₁ := eq20297
       have r₂ := eq3490 y x
       grind)
    | (have r₁ := eq20297
       have r₂ := eq3490 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq20297
       have r₂ := eq3490 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq20297 eq3490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3490 eq20297
  have eq20339 : (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq20338
  have eq20341 : x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq20339
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq20339
       have r₂ := eq13 x y
       grind)
    | exact resolve eq20339 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20339
  have eq20343 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20341
       grind)
    | exact superpose eq20341 eq16
    | exact resolve eq16 eq20341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20341
  have eq20344 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20343
       have r₂ := eq22 x
       grind)
    | exact resolve eq20343 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20343
  have eq20380 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq17971 x y
       have i₂ := eq20344
       grind)
    | exact superpose eq20344 eq17971
    | (have j0 := eq17971 y x
       grind)
    | (have r₁ := eq17971 x y
       have r₂ := eq20344
       grind)
    | exact resolve eq17971 eq20344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17971
  have eq20385 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20380
  have eq20393 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20385
       grind)
    | exact superpose eq20385 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20385
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20385
       grind)
    | exact resolve eq13 eq20385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20385
  have eq20400 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq20393
  have eq20401 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq20400
  have eq20402 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20401
       grind)
    | exact superpose eq20401 eq16
    | exact resolve eq16 eq20401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20401
  have eq20403 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20402
       have r₂ := eq22 x
       grind)
    | exact resolve eq20402 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20402
  have eq20405 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3631
       have i₂ := eq20403
       grind)
    | exact superpose eq20403 eq3631
    | exact resolve eq3631 eq20403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3631 eq20403
  have eq20409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq20405
  have eq20410 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq20409
  have eq20418 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq20410
       grind)
    | exact superpose eq20410 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20410
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq20410
       grind)
    | exact resolve eq13 eq20410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20410
  have eq20422 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq20418
  have eq20423 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq20422
  have eq20430 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20423
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20423
    | exact resolve eq20423 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20423
  have eq20922 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20430
       grind)
    | exact superpose eq20430 eq16
    | exact resolve eq16 eq20430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20430
  have eq20965 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20922
       have i₂ := eq20344
       grind)
    | exact superpose eq20344 eq20922
    | exact resolve eq20922 eq20344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20344 eq20922
  have eq20968 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq20965
  have eq20969 : (σ x) = (σ y) := by grind
  clear eq20968
  have eq20970 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20969
       grind)
    | exact superpose eq20969 eq16
    | exact resolve eq16 eq20969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20971 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq20969
       grind)
    | exact superpose eq20969 eq10
    | exact resolve eq10 eq20969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20969
  have eq21139 : x = y := by
    first
    | (have i₁ := eq20971
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq20971
    | exact resolve eq20971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20971
  have eq21140 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq20970
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq20970
    | exact resolve eq20970 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20970
  have eq21141 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq21140
       have i₂ := eq21139
       grind)
    | exact superpose eq21139 eq21140
    | exact resolve eq21140 eq21139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21139 eq21140
  have eq21142 : False := by grind
  exact eq21142

/-- `Equation177`: `x = (y ◇ y) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pxx_pxx_pyx_Equation177 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law177 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law177.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X1)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0)
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1) (M.op X0 X1)
       have i₂ := eq16 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : x = (M.op (M.op y y) (M.op x y)) := by
    first
    | (have i₁ := eq16 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) x) := by
    first
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (M.op y y)) := by
    first
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq40 eq16
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq47 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq48 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq49 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq52 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq53 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq54 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (σ (k X1 (k x X0))) = (k (σ X1) (k (σ x) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (k x X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq48 X0
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq60 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq49 X0
       grind)
    | exact superpose eq49 eq15
    | exact resolve eq15 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq15
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq57
    | (have j0 := eq57 x
       grind)
    | exact resolve eq57 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq120 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq60 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq60
    | (have j0 := eq60 x
       grind)
    | exact resolve eq60 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq60 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq60
    | (have j0 := eq60 y
       grind)
    | exact resolve eq60 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq154 : y ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : x ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
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
  have eq326 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq47 X0 X1
       grind)
    | exact superpose eq47 eq15
    | exact resolve eq15 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq410 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq326 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq326
    | exact resolve eq326 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : (M.op x x) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq35 y (M.op x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq35
    | exact resolve eq35 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : y = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq554 eq35
    | exact resolve eq35 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq46 eq35
    | exact resolve eq35 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq582 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq575 eq35
    | exact resolve eq35 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq604 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (k X0 X1)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq39
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : (σ x) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq637
  have eq656 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq611 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq672 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq613 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq613 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq613 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | exact resolve eq613 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq688 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq672 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq672 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq672 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq691 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq604
       grind)
    | exact superpose eq604 eq52
    | exact resolve eq52 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq692 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq691
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq691
    | exact resolve eq691 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq694 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq692
    | exact resolve eq692 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq694 eq607
    | exact resolve eq607 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq702
       have r₂ := eq27
       grind)
    | exact resolve eq702 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq716 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq709 eq155
    | (have r₁ := eq155
       have r₂ := eq709
       grind)
    | exact resolve eq155 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq723 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq716
  have eq725 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq723
       have r₂ := eq163
       grind)
    | exact resolve eq723 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq723
  have eq727 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq694 eq725
    | exact resolve eq725 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq725
  have eq733 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq727
       grind)
    | exact resolve eq13 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727 eq16
    | exact resolve eq16 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq737 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq733
  have eq739 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq737
       have r₂ := eq735
       grind)
    | exact resolve eq737 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq737
  have eq755 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq736 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq736 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq736
       grind)
    | exact resolve eq13 eq736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq759 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq755
  have eq761 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq759
       have r₂ := eq757
       grind)
    | exact resolve eq759 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq759
  have eq763 : (τ (σ (M.op x y))) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq739 eq128
    | exact resolve eq128 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq763
    | exact resolve eq763 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq763
  have eq1337 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq36
    | exact resolve eq36 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1426 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1337 X0 X1
       have i₂ := eq16 X0 X0
       grind)
    | exact superpose eq16 eq1337
    | exact resolve eq1337 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1451 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 y)) = X0 ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq656 y X0
       have i₂ := eq768
       grind)
    | exact superpose eq768 eq656
    | (have j0 := eq656 y x
       grind)
    | exact resolve eq656 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1500 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq35 X0 (k X0 X0)
       have i₂ := eq656 X0 X0
       grind)
    | exact superpose eq656 eq35
    | (have j1 := eq656 X0 x
       grind)
    | exact resolve eq35 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1507 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1500 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1500 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq1500 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500
  have eq1669 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1451 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1451
    | (have j0 := eq1451 x
       grind)
    | exact resolve eq1451 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq1686 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1669
       have i₂ := eq1507 sF0
       grind)
    | exact superpose eq1507 eq1669
    | exact resolve eq1669 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq1698 : y = (k y y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1686
       have i₂ := eq1507 y
       grind)
    | exact superpose eq1507 eq1686
    | exact resolve eq1686 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq1709 : y = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq768 eq1698
    | exact resolve eq1698 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq1698
  have eq1710 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1709
  have eq1719 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1710 eq54
    | exact resolve eq54 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq1726 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1719
    | exact resolve eq1719 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq1730 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1726
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1726
    | exact resolve eq1726 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1876 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1730 eq761
    | exact resolve eq761 eq1730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761 eq1730
  have eq1885 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1876
  have eq1903 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1885 eq26
    | exact resolve eq26 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1930 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1885 eq739
    | exact resolve eq739 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq1885
  have eq1949 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1930
  have eq1984 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1903
       have i₂ := eq1507 sF2
       grind)
    | exact superpose eq1507 eq1903
    | exact resolve eq1903 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq1990 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1949 eq1984
    | exact resolve eq1984 eq1949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949 eq1984
  have eq1993 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1990
       have r₂ := eq27
       grind)
    | exact resolve eq1990 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq1995 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1993
       grind)
    | exact superpose eq1993 eq18
    | exact resolve eq18 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1996 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1993
       grind)
    | exact superpose eq1993 eq24
    | exact resolve eq24 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1997 : x = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37
       have i₂ := eq1993
       grind)
    | exact superpose eq1993 eq37
    | exact resolve eq37 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2001 : (M.op x y) ≠ (M.op x y) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq154
       have i₂ := eq1993
       grind)
    | exact superpose eq1993 eq154
    | (have r₁ := eq154
       have r₂ := eq1993
       grind)
    | exact resolve eq154 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq2002 : (M.op x x) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq554
       have i₂ := eq1993
       grind)
    | exact superpose eq1993 eq554
    | exact resolve eq554 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq2005 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq2001
  have eq2007 : (M.op x x) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2002
       have i₂ := eq1507 sF0
       grind)
    | exact superpose eq1507 eq2002
    | exact resolve eq2002 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2008 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2005
       have i₂ := eq1507 sF0
       grind)
    | exact superpose eq1507 eq2005
    | exact resolve eq2005 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005
  have eq2012 : x = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1997
       have i₂ := eq1507 sF0
       grind)
    | exact superpose eq1507 eq1997
    | exact resolve eq1997 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997
  have eq2013 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1996
    | exact resolve eq1996 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq2014 : (k x x) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2007
       have i₂ := eq1507 x
       grind)
    | exact superpose eq1507 eq2007
    | exact resolve eq2007 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2007
  have eq2142 : (k (σ (M.op x y)) (σ x)) = (σ (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2008 eq52
    | exact resolve eq52 eq2008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq2008
  have eq2146 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq54 eq2142
    | exact resolve eq2142 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2142
  have eq2148 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2146
    | exact resolve eq2146 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2150 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2013 eq2148
    | exact resolve eq2148 eq2013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq2157 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2012 eq36
    | exact resolve eq36 eq2012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2167 : (M.op (M.op x y) (M.op x y)) = (M.op (k x x) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2157
       have i₂ := eq1507 x
       grind)
    | exact superpose eq1507 eq2157
    | exact resolve eq2157 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157
  have eq2171 : (k (M.op x y) (M.op x y)) = (M.op (k x x) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2167
       have i₂ := eq1507 sF0
       grind)
    | exact superpose eq1507 eq2167
    | exact resolve eq2167 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq2189 : ∀ X0 : G, (M.op (k (σ y) (σ x)) (M.op X0 (σ y))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2150 eq656
    | (have j0 := eq656 (σ y) x
       grind)
    | exact resolve eq656 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2197 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (M.op (k (σ y) (σ x)) (M.op X0 (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2189 X0
       have i₂ := eq1507 sF3
       grind)
    | exact superpose eq1507 eq2189
    | (have j0 := eq2189 X0
       grind)
    | exact resolve eq2189 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189
  have eq2201 : ∀ X0 : G, (M.op (k (σ y) (σ x)) (M.op X0 (σ y))) = X0 ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2150 eq2197
    | (have j0 := eq2197 X0
       grind)
    | exact resolve eq2197 eq2150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150 eq2197
  have eq2365 : (M.op x y) = (M.op (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2014 eq16
    | exact resolve eq16 eq2014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq2368 : (M.op x y) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2365
       have i₂ := eq1507 (k sF0 sF0)
       grind)
    | exact superpose eq1507 eq2365
    | exact resolve eq2365 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq2742 : (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (M.op (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2171 eq36
    | exact resolve eq36 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq2752 : (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2742
       have i₂ := eq1507 (k sF0 sF0)
       grind)
    | exact superpose eq1507 eq2742
    | exact resolve eq2742 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742
  have eq2757 : (M.op x y) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2368 eq2752
    | exact resolve eq2752 eq2368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2752
  have eq3039 : (M.op (k x x) (k x x)) = (M.op (M.op (M.op x y) (M.op x y)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2368 eq36
    | exact resolve eq36 eq2368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2368
  have eq3047 : (M.op (k x x) (k x x)) = (M.op (k (M.op x y) (M.op x y)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3039
       have i₂ := eq1507 sF0
       grind)
    | exact superpose eq1507 eq3039
    | exact resolve eq3039 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3039
  have eq3052 : (k (k x x) (k x x)) = (M.op (k (M.op x y) (M.op x y)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3047
       have i₂ := eq1507 (k x x)
       grind)
    | exact superpose eq1507 eq3047
    | exact resolve eq3047 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3047
  have eq3055 : (k (k x x) (k x x)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2757 eq3052
    | exact resolve eq3052 eq2757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052
  have eq3057 : x = (k (k x x) (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2012 eq3055
    | exact resolve eq3055 eq2012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012 eq3055
  have eq3485 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq607 eq2201
    | exact resolve eq2201 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3491 : (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2201
    | (have j0 := eq2201 (σ x)
       grind)
    | exact resolve eq2201 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq3509 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3485 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3485
  have eq3532 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq607 eq3491
    | exact resolve eq3491 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq3546 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3532
  have eq3557 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3546
       have i₂ := eq1507 sF4
       grind)
    | exact superpose eq1507 eq3546
    | exact resolve eq3546 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3546
  have eq3606 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3509 eq35
    | exact resolve eq35 eq3509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3509
  have eq3627 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3606
       have i₂ := eq1507 sF3
       grind)
    | exact superpose eq1507 eq3606
    | exact resolve eq3606 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3606
  have eq3643 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3627 eq128
    | exact resolve eq128 eq3627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq3627
  have eq3665 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq709 eq3643
    | exact resolve eq3643 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq3643
  have eq3683 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3665 eq2757
    | exact resolve eq2757 eq3665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757 eq3665
  have eq3696 : (M.op x y) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3683
  have eq3718 : (M.op x y) = (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3696
       have i₂ := eq410 sF4 sF4
       grind)
    | exact superpose eq410 eq3696
    | exact resolve eq3696 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq3696
  have eq3724 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3557 eq3718
    | exact resolve eq3718 eq3557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3557 eq3718
  have eq3729 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq3724
    | exact resolve eq3724 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq3730 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3729
  have eq3733 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3730 eq27
    | exact resolve eq27 eq3730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3730
  have eq3766 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3733
       have r₂ := eq2013
       grind)
    | exact resolve eq3733 eq2013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3733
  have eq3774 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3766 eq27
    | exact resolve eq27 eq3766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3780 : (σ y) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3766 eq582
    | exact resolve eq582 eq3766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq3799 : (σ y) = (M.op (σ x) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3780
       have i₂ := eq1507 sF2
       grind)
    | exact superpose eq1507 eq3780
    | exact resolve eq3780 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3780
  have eq3808 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2013 eq3774
    | exact resolve eq3774 eq2013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013 eq3774
  have eq3811 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq3808
  have eq3823 : (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (k (σ x) (σ x))) ∨ (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq3799
       have i₂ := eq11 (k sF2 sF2) sF2
       grind)
    | exact superpose eq11 eq3799
    | (have j1 := eq11 (k (σ x) (σ x)) (σ x)
       grind)
    | exact resolve eq3799 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3826 : (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3799 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3844 : (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3826
       have r₂ := eq3811
       grind)
    | exact resolve eq3826 eq3811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3826
  have eq3845 : (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | exact superpose eq3799 eq3823
    | exact resolve eq3823 eq3799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3799 eq3823
  have eq3848 : (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (k (σ x) (σ x)) = (M.op (σ x) (k (σ x) (σ x))) := by
    first
    | (have r₁ := eq3845
       have r₂ := eq3811
       grind)
    | exact resolve eq3845 eq3811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845
  have eq3851 : (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3844 eq3848
    | exact resolve eq3848 eq3844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3844 eq3848
  have eq3853 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq3851
    | exact resolve eq3851 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851
  have eq3854 : (σ x) = (σ y) ∨ (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3766 eq3853
    | exact resolve eq3853 eq3766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3766 eq3853
  have eq3855 : (σ y) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3854
       have r₂ := eq3811
       grind)
    | exact resolve eq3854 eq3811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3811 eq3854
  have eq3887 : (τ (σ y)) = (k (τ (k (σ x) (σ x))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3855 eq170
    | exact resolve eq170 eq3855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq3855
  have eq3900 : (τ (σ y)) = (k (k x x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110 eq3887
    | exact resolve eq3887 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq3903 : y = (k (k x x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq3900
    | exact resolve eq3900 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3900
  have eq3906 : (M.op x y) = (k (k x x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1993 eq3903
    | exact resolve eq3903 eq1993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993 eq3903
  have eq3915 : x = (M.op (M.op (k x x) (k x x)) (M.op x y)) ∨ x = (M.op x (k x x)) ∨ (k x x) = (M.op x (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq614 (k x x) x
       have i₂ := eq3906
       grind)
    | exact superpose eq3906 eq614
    | (have j0 := eq614 (k x x) x
       grind)
    | exact resolve eq614 eq3906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3923 : x = (M.op (k (k x x) (k x x)) (M.op x y)) ∨ x = (M.op x (k x x)) ∨ (k x x) = (M.op x (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3915
       have i₂ := eq1507 (k x x)
       grind)
    | exact superpose eq1507 eq3915
    | exact resolve eq3915 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3915
  have eq3925 : x = (M.op x (M.op x y)) ∨ x = (M.op x (k x x)) ∨ (k x x) = (M.op x (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3057 eq3923
    | exact resolve eq3923 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057 eq3923
  have eq3927 : x = (M.op x y) ∨ x = (M.op x (k x x)) ∨ (k x x) = (M.op x (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1995 eq3925
    | exact resolve eq3925 eq1995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995 eq3925
  have eq3928 : (k x x) = (M.op x (k x x)) ∨ x = (M.op x (k x x)) ∨ x = (M.op x y) := by grind
  clear eq3927
  have eq4111 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0
       have i₂ := eq1507 (M.op X0 X0)
       grind)
    | exact superpose eq1507 eq16
    | exact resolve eq16 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4149 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4111 X0
       have i₂ := eq1507 X0
       grind)
    | exact superpose eq1507 eq4111
    | exact resolve eq4111 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111
  have eq5814 : (k x x) ≠ (k x x) ∨ (M.op (k x x) (k x x)) = (k (k x x) x) ∨ x = (M.op x (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (k x x) x
       have i₂ := eq3928
       grind)
    | exact superpose eq3928 eq13
    | (have j0 := eq13 (k x x) x
       grind)
    | (have r₁ := eq13 (k x x) x
       have r₂ := eq3928
       grind)
    | exact resolve eq13 eq3928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3928
  have eq5823 : (M.op (k x x) (k x x)) = (k (k x x) x) ∨ x = (M.op x (k x x)) ∨ x = (M.op x y) := by grind
  clear eq5814
  have eq5834 : (M.op (k x x) (k x x)) = (k (k x x) x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq28 (k x x) x
       grind)
    | (have r₁ := eq5823
       have r₂ := eq28 (k x x) x
       grind)
    | (have r₁ := eq5823
       have r₂ := eq28 y x
       grind)
    | exact resolve eq5823 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5823
  have eq5843 : (k (k x x) (k x x)) = (k (k x x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5834
       have i₂ := eq1507 (k x x)
       grind)
    | exact superpose eq1507 eq5834
    | exact resolve eq5834 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5834
  have eq5845 : x = (k (k x x) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5843
       have i₂ := eq4149 x
       grind)
    | exact superpose eq4149 eq5843
    | exact resolve eq5843 eq4149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149 eq5843
  have eq5848 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3906 eq5845
    | exact resolve eq5845 eq3906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3906 eq5845
  have eq5849 : x = (M.op x y) := by grind
  clear eq5848
  have eq5850 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq18
    | exact resolve eq18 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5851 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq22
    | exact resolve eq22 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq5852 : (M.op y y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq38
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq38
    | exact resolve eq38 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq5853 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op y y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq45
    | exact resolve eq45 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq5857 : (M.op x y) ≠ (M.op x y) ∨ (M.op y y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq162
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq162
    | (have r₁ := eq162
       have r₂ := eq5849
       grind)
    | exact resolve eq162 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq5858 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq561
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq561
    | exact resolve eq561 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq5859 : (M.op y y) = (k y (M.op x y)) := by grind
  clear eq5857
  have eq5861 : y = (M.op (M.op x y) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq5858
       have i₂ := eq1507 sF0
       grind)
    | exact superpose eq1507 eq5858
    | exact resolve eq5858 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858
  have eq5862 : (k y y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq5859
       have i₂ := eq1507 y
       grind)
    | exact superpose eq1507 eq5859
    | exact resolve eq5859 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5859
  have eq5864 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (k y y)) := by
    first
    | (have i₁ := eq5853
       have i₂ := eq1507 y
       grind)
    | exact superpose eq1507 eq5853
    | exact resolve eq5853 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5853
  have eq5865 : (M.op y y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq5852
       have i₂ := eq1507 sF0
       grind)
    | exact superpose eq1507 eq5852
    | exact resolve eq5852 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5852
  have eq5867 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (k y (M.op x y))) := by
    first
    | (have i₁ := eq5864
       have i₂ := eq5862
       grind)
    | exact superpose eq5862 eq5864
    | exact resolve eq5864 eq5862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5864
  have eq5868 : (k y y) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq5865
       have i₂ := eq1507 y
       grind)
    | exact superpose eq1507 eq5865
    | exact resolve eq5865 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5865
  have eq5870 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (k y (M.op x y))) := by
    first
    | (have i₁ := eq5867
       have i₂ := eq1507 sF0
       grind)
    | exact superpose eq1507 eq5867
    | exact resolve eq5867 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5867
  have eq5871 : (k y (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq5868
       have i₂ := eq5862
       grind)
    | exact superpose eq5862 eq5868
    | exact resolve eq5868 eq5862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5868
  have eq5873 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5851 eq20
    | exact resolve eq20 eq5851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5883 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5851 eq326
    | exact resolve eq326 eq5851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq5991 : (M.op x y) = (M.op (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq5850 eq16
    | exact resolve eq16 eq5850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6004 : (M.op x y) = (M.op (k y y) (M.op x y)) := by
    first
    | (have i₁ := eq5991
       have i₂ := eq1507 y
       grind)
    | exact superpose eq1507 eq5991
    | exact resolve eq5991 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5991
  have eq6008 : (M.op x y) = (M.op (k y (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq6004
       have i₂ := eq5862
       grind)
    | exact superpose eq5862 eq6004
    | exact resolve eq6004 eq5862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6004
  have eq6056 : (k (σ y) (σ y)) = (σ (k y (M.op x y))) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq5862
       grind)
    | exact superpose eq5862 eq53
    | exact resolve eq53 eq5862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6057 : ∀ X0 : G, (M.op (k y (M.op x y)) (M.op X0 y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq656 y X0
       have i₂ := eq5862
       grind)
    | exact superpose eq5862 eq656
    | (have j0 := eq656 y x
       grind)
    | exact resolve eq656 eq5862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6069 : ∀ X0 : G, y = (k y y) ∨ (M.op (k y (M.op x y)) (M.op X0 y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq6057 X0
       have i₂ := eq1507 y
       grind)
    | exact superpose eq1507 eq6057
    | (have j0 := eq6057 X0
       grind)
    | exact resolve eq6057 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6057
  have eq6070 : (k (σ y) (σ y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq54 eq6056
    | exact resolve eq6056 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6056
  have eq6077 : ∀ X0 : G, (M.op (k y (M.op x y)) (M.op X0 y)) = X0 ∨ y = (k y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq6069 X0
       have i₂ := eq5862
       grind)
    | exact superpose eq5862 eq6069
    | (have j0 := eq6069 X0
       grind)
    | exact resolve eq6069 eq5862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6069
  have eq6078 : (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq5873 eq6070
    | exact resolve eq6070 eq5873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6070
  have eq6081 : (k (σ y) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq6078
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6078
    | exact resolve eq6078 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6078
  have eq6098 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op (k y (M.op x y)) (k y (M.op x y))) := by
    first
    | exact superpose eq6008 eq1426
    | exact resolve eq1426 eq6008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq6100 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (k (k y (M.op x y)) (k y (M.op x y))) := by
    first
    | (have i₁ := eq6098
       have i₂ := eq1507 (k y sF0)
       grind)
    | exact superpose eq1507 eq6098
    | exact resolve eq6098 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6098
  have eq6108 : (M.op (M.op x y) (k (M.op x y) (M.op x y))) = (k (k y (M.op x y)) (k y (M.op x y))) := by
    first
    | (have i₁ := eq6100
       have i₂ := eq1507 sF0
       grind)
    | exact superpose eq1507 eq6100
    | exact resolve eq6100 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6100
  have eq6110 : y = (k (k y (M.op x y)) (k y (M.op x y))) := by
    first
    | exact superpose eq5861 eq6108
    | exact resolve eq6108 eq5861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5861 eq6108
  have eq6115 : (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6081 eq646
    | exact resolve eq646 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq6122 : (σ y) = (M.op (M.op (σ y) (σ y)) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6081 eq614
    | (have j0 := eq614 (σ y) (σ y)
       grind)
    | exact resolve eq614 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6129 : (σ y) = (M.op (M.op (σ y) (σ y)) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6122
  have eq6132 : (σ y) = (M.op (k (σ y) (σ y)) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6129
       have i₂ := eq1507 sF3
       grind)
    | exact superpose eq1507 eq6129
    | exact resolve eq6129 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6129
  have eq6136 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq6115
       have i₂ := eq1507 sF3
       grind)
    | exact superpose eq1507 eq6115
    | exact resolve eq6115 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6115
  have eq6140 : (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6081 eq6132
    | exact resolve eq6132 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6132
  have eq6144 : (σ x) = (M.op (k (σ y) (σ x)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq6081 eq6136
    | exact resolve eq6136 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6136
  have eq6146 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6140
       have i₂ := eq1507 (k sF3 sF2)
       grind)
    | exact superpose eq1507 eq6140
    | exact resolve eq6140 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6140
  have eq6149 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq6146
       have i₂ := eq1507 sF3
       grind)
    | exact superpose eq1507 eq6146
    | exact resolve eq6146 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6146
  have eq6150 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq6081 eq6149
    | exact resolve eq6149 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6149
  have eq6373 : (k (τ (σ y)) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq607 eq5883
    | exact resolve eq5883 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5883
  have eq6416 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq6373
    | exact resolve eq6373 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6373
  have eq6636 : (k (M.op x y) (M.op x y)) ≠ (k (M.op x y) (M.op x y)) ∨ (M.op (k y (M.op x y)) (k y (M.op x y))) = (k (k y (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq5870 eq28
    | (have j0 := eq28 (k y (M.op x y)) (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq28 (k y (M.op x y)) (k (M.op x y) (M.op x y))
       have r₂ := eq5870
       grind)
    | exact resolve eq28 eq5870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5870
  have eq6642 : (M.op (k y (M.op x y)) (k y (M.op x y))) = (k (k y (M.op x y)) (k (M.op x y) (M.op x y))) := by grind
  clear eq6636
  have eq6647 : (k (k y (M.op x y)) (k y (M.op x y))) = (k (k y (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq6642
       have i₂ := eq1507 (k y sF0)
       grind)
    | exact superpose eq1507 eq6642
    | exact resolve eq6642 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6642
  have eq6653 : y = (k (k y (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq6110 eq6647
    | exact resolve eq6647 eq6110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6647
  have eq6705 : ∀ X0 : G, (σ (k X0 (k x (M.op x y)))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq5851 eq55
    | exact resolve eq55 eq5851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq6718 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq6705 X0
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq6705
    | exact resolve eq6705 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6705
  have eq6840 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq607 eq6144
    | exact resolve eq6144 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6144
  have eq6856 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6840
  have eq6866 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6856
       have i₂ := eq1507 sF4
       grind)
    | exact superpose eq1507 eq6856
    | exact resolve eq6856 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6856
  have eq6877 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6866 eq656
    | (have j0 := eq656 (M.op (σ x) (σ y)) x
       grind)
    | exact resolve eq656 eq6866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq6887 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6877 X0
       have i₂ := eq1507 sF4
       grind)
    | exact superpose eq1507 eq6877
    | (have j0 := eq6877 X0
       grind)
    | exact resolve eq6877 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6877
  have eq6889 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq6866 eq6887
    | (have j0 := eq6887 X0
       grind)
    | exact resolve eq6887 eq6866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6887
  have eq6890 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6889 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6889
  have eq6898 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6416 eq6008
    | exact resolve eq6008 eq6416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6008
  have eq7017 : (σ y) = (k (σ (k y (M.op x y))) (k (σ x) (σ x))) := by
    first
    | exact superpose eq6653 eq6718
    | exact resolve eq6718 eq6653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6653 eq6718
  have eq7077 : (σ y) = (k (k (σ y) (σ (M.op x y))) (k (σ x) (σ x))) := by
    first
    | exact superpose eq54 eq7017
    | exact resolve eq7017 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq7017
  have eq7097 : (σ y) = (k (k (σ y) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq5873 eq7077
    | exact resolve eq7077 eq5873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7077
  have eq7114 : (σ y) = (k (k (σ y) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq7097
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7097
    | exact resolve eq7097 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7097
  have eq7139 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) := by
    first
    | exact superpose eq7114 eq688
    | (have j0 := eq688 (σ y) (σ x)
       grind)
    | exact resolve eq688 eq7114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688 eq7114
  have eq7140 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7139
       have i₂ := eq1507 (k sF3 sF2)
       grind)
    | exact superpose eq1507 eq7139
    | exact resolve eq7139 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7139
  have eq7143 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) := by
    first
    | (have r₁ := eq7140
       have r₂ := eq6150
       grind)
    | exact resolve eq7140 eq6150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6150 eq7140
  have eq7146 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq607 eq7143
    | exact resolve eq7143 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq7143
  have eq7165 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6866 eq7146
    | exact resolve eq7146 eq6866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7146
  have eq7172 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7165 eq39
    | exact resolve eq39 eq7165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7165
  have eq7202 : (σ x) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7172
       have i₂ := eq1507 sF3
       grind)
    | exact superpose eq1507 eq7172
    | exact resolve eq7172 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7172
  have eq7208 : (σ x) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6081 eq7202
    | exact resolve eq7202 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7202
  have eq7362 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6890 sF4
       have i₂ := eq1507 sF4
       grind)
    | exact superpose eq1507 eq6890
    | exact resolve eq6890 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6890
  have eq7394 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6866 eq7362
    | exact resolve eq7362 eq6866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6866 eq7362
  have eq7405 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7394
       have i₂ := eq1507 sF2
       grind)
    | exact superpose eq1507 eq7394
    | exact resolve eq7394 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7394
  have eq7418 : (k x x) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7405 eq110
    | exact resolve eq110 eq7405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq7405
  have eq7497 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7418
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq7418
    | exact resolve eq7418 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7418
  have eq7549 : (k y (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7497 eq5871
    | exact resolve eq5871 eq7497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5871 eq7497
  have eq7586 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6416 eq7549
    | exact resolve eq7549 eq6416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6416 eq7549
  have eq7598 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6898 eq7586
    | exact resolve eq7586 eq6898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6898 eq7586
  have eq7626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7598 eq14
    | exact resolve eq14 eq7598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7598
  have eq7634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq7626
    | exact resolve eq7626 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7626
  have eq7638 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7634
       have r₂ := eq27
       grind)
    | exact resolve eq7634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7634
  have eq7642 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7638 eq39
    | exact resolve eq39 eq7638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq7661 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7638
  have eq7672 : (σ x) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7642
       have i₂ := eq1507 sF3
       grind)
    | exact superpose eq1507 eq7642
    | exact resolve eq7642 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7642
  have eq7679 : (σ x) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6081 eq7672
    | exact resolve eq7672 eq6081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6081 eq7672
  have eq7734 : (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7679 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq7679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7752 : (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7734
       have r₂ := eq7661
       grind)
    | exact resolve eq7734 eq7661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7734
  have eq8471 : (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq7208
       have i₂ := eq11 sF3 (k sF3 sF2)
       grind)
    | exact superpose eq11 eq7208
    | (have j1 := eq11 (σ y) (k (σ y) (σ x))
       grind)
    | exact resolve eq7208 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7208
  have eq8495 : (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | (have r₁ := eq8471
       have r₂ := eq7661
       grind)
    | exact resolve eq8471 eq7661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8471
  have eq8505 : (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq7752 eq8495
    | exact resolve eq8495 eq7752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7752 eq8495
  have eq8512 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq26 eq8505
    | exact resolve eq8505 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8505
  have eq8513 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by grind
  clear eq8512
  have eq8518 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7679 eq8513
    | exact resolve eq8513 eq7679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7679 eq8513
  have eq8520 : (σ x) = (k (σ y) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8518
       have r₂ := eq7661
       grind)
    | exact resolve eq8518 eq7661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8518
  have eq8527 : (τ (σ x)) = (k y (τ (k (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8520 eq120
    | exact resolve eq120 eq8520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq8520
  have eq8537 : (τ (σ x)) = (k y (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq127 eq8527
    | exact resolve eq8527 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq8527
  have eq8540 : (τ (σ x)) = (k y (k y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8537
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq8537
    | exact resolve eq8537 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8537
  have eq8541 : x = (k y (k y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq8540
    | exact resolve eq8540 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq8540
  have eq8542 : (M.op x y) = (k y (k y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8541
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq8541
    | exact resolve eq8541 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8541
  have eq8549 : (M.op (M.op y y) (M.op x y)) = (k y (M.op x y)) ∨ (k y (M.op x y)) = (M.op (k y (M.op x y)) y) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8542 eq614
    | (have j0 := eq614 y (k y (M.op x y))
       grind)
    | exact resolve eq614 eq8542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq8551 : (M.op x y) ≠ (k y (M.op x y)) ∨ (k y (M.op x y)) = (M.op (k y (M.op x y)) y) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8542 eq642
    | (have j0 := eq642 (k y (M.op x y)) y
       grind)
    | exact resolve eq642 eq8542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq8558 : x = (k y (M.op x y)) ∨ (k y (M.op x y)) = (M.op (k y (M.op x y)) y) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37 eq8549
    | exact resolve eq8549 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq8549
  have eq8563 : (M.op x y) = (k y (M.op x y)) ∨ (k y (M.op x y)) = (M.op (k y (M.op x y)) y) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8558
       have i₂ := eq5849
       grind)
    | exact superpose eq5849 eq8558
    | exact resolve eq8558 eq5849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5849 eq8558
  have eq8566 : (k y (M.op x y)) = (M.op (k y (M.op x y)) y) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8563
       have r₂ := eq8551
       grind)
    | exact resolve eq8563 eq8551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8551 eq8563
  have eq61554 : (k y (M.op x y)) = (M.op (k y (M.op x y)) (k y (M.op x y))) ∨ y = (k y (M.op x y)) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8566 eq6077
    | exact resolve eq6077 eq8566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6077
  have eq61559 : (k y (M.op x y)) ≠ (k y (M.op x y)) ∨ (M.op y y) = (k y (k y (M.op x y))) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8566 eq28
    | (have j0 := eq28 y (k y (M.op x y))
       grind)
    | (have r₁ := eq28 y (k y (M.op x y))
       have r₂ := eq8566
       grind)
    | (have r₁ := eq28 (σ y) (σ x)
       have r₂ := eq8566
       grind)
    | exact resolve eq28 eq8566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq61564 : y ≠ (k y (M.op x y)) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8566
  have eq61566 : (M.op y y) = (k y (k y (M.op x y))) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq61559
  have eq61573 : (M.op y y) = (k y (k y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y (k y (M.op x y))
       grind)
    | (have r₁ := eq61566
       have r₂ := eq13 y (k y (M.op x y))
       grind)
    | exact resolve eq61566 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61566
  have eq61576 : (k y (M.op x y)) = (M.op (k y (M.op x y)) (k y (M.op x y))) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq61554
       have r₂ := eq61564
       grind)
    | exact resolve eq61554 eq61564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61554
  have eq61581 : (k y y) = (k y (k y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61573
       have i₂ := eq1507 y
       grind)
    | exact superpose eq1507 eq61573
    | exact resolve eq61573 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61573
  have eq61584 : (k y (M.op x y)) = (k (k y (M.op x y)) (k y (M.op x y))) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61576
       have i₂ := eq1507 (k y sF0)
       grind)
    | exact superpose eq1507 eq61576
    | exact resolve eq61576 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507 eq61576
  have eq61588 : (k y (M.op x y)) = (k y (k y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61581
       have i₂ := eq5862
       grind)
    | exact superpose eq5862 eq61581
    | exact resolve eq61581 eq5862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5862 eq61581
  have eq61591 : y = (k y (M.op x y)) ∨ y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6110 eq61584
    | exact resolve eq61584 eq6110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6110 eq61584
  have eq61595 : (M.op x y) = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8542 eq61588
    | exact resolve eq61588 eq8542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8542 eq61588
  have eq61598 : y = (M.op (k y (M.op x y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq61591
       have r₂ := eq61564
       grind)
    | exact resolve eq61591 eq61564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61564 eq61591
  have eq61602 : y = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq61595 eq61598
    | exact resolve eq61598 eq61595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61595 eq61598
  have eq61606 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5850 eq61602
    | exact resolve eq61602 eq5850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5850 eq61602
  have eq61617 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61606 eq27
    | exact resolve eq27 eq61606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61606
  have eq61658 : y = (M.op x y) := by
    first
    | (have r₁ := eq61617
       have r₂ := eq5873
       grind)
    | exact resolve eq61617 eq5873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61617
  have eq61664 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq61658
       grind)
    | exact superpose eq61658 eq24
    | exact resolve eq24 eq61658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq61658
  have eq61804 : (σ x) = (σ y) := by
    first
    | exact superpose eq5851 eq61664
    | exact resolve eq61664 eq5851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5851 eq61664
  have eq61939 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq61804 eq7661
    | (have r₁ := eq7661
       have r₂ := eq61804
       grind)
    | exact resolve eq7661 eq61804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7661 eq61804
  have eq62008 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq61939
  have eq62171 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq62008 eq27
    | exact resolve eq27 eq62008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq62008
  have eq62205 : False := by grind
  exact eq62205

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pyy_y_pxy_pxx_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x
       grind)
    | exact resolve eq15 eq22
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq186
       grind)
    | exact superpose eq186 eq41
    | exact resolve eq41 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq420 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq419
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq419
    | exact resolve eq419 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq422 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq420
    | exact resolve eq420 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq511 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq422 eq187
    | exact resolve eq187 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187 eq422
  have eq518 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq511
       have r₂ := eq27
       grind)
    | exact resolve eq511 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq628 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq518 eq13
    | exact resolve eq13 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq632 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq628
  have eq636 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq633
       have i₂ := eq632 y
       grind)
    | exact superpose eq632 eq633
    | exact resolve eq633 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq670 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) := by
    first
    | exact superpose eq636 eq153
    | exact resolve eq153 eq636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq636
  have eq674 : y = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq32 eq670
    | exact resolve eq670 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq670
  have eq675 : y = (k y y) := by grind
  clear eq674
  have eq681 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq41
    | exact resolve eq41 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq685 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq681
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq681
    | exact resolve eq681 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq681
  have eq1361 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq16
    | exact resolve eq16 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1362 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq175
    | exact resolve eq175 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq176
    | exact resolve eq176 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1365 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq198 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq198
    | exact resolve eq198 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq1375 : ∀ X0 X1 : G, (M.op (M.op X0 (k X0 X0)) (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq16
    | exact resolve eq16 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1385 : ∀ X0 X1 : G, (M.op (M.op X0 (k X0 X0)) (k X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1375 X0 X1
       have i₂ := eq632 X1
       grind)
    | exact superpose eq632 eq1375
    | exact resolve eq1375 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1415 : x = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq1362 y
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq1362
    | exact resolve eq1362 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1461 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq176 eq178
    | exact resolve eq178 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1464 : ∀ X0 : G, (M.op (M.op x (M.op x y)) (M.op X0 X0)) = (M.op (M.op x (M.op x y)) x) := by
    intro X0
    first
    | exact superpose eq1415 eq178
    | exact resolve eq178 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1415
  have eq1589 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq175 eq1464
    | exact resolve eq1464 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq1592 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq176 eq1461
    | exact resolve eq1461 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1461
  have eq1751 : x ≠ (M.op x x) ∨ x = (k (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq1589 eq13
    | exact resolve eq13 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1753 : x = (k (M.op x (M.op x y)) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1589 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq1761 : x = (k (M.op x (M.op x y)) x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq1753
       have i₂ := eq632 x
       grind)
    | exact superpose eq632 eq1753
    | exact resolve eq1753 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1753
  have eq1762 : x ≠ (k x x) ∨ x = (k (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq1751
       have i₂ := eq632 x
       grind)
    | exact superpose eq632 eq1751
    | exact resolve eq1751 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751
  have eq1766 : x = (k (M.op x (M.op x y)) x) := by
    first
    | (have r₁ := eq1762
       have r₂ := eq1761
       grind)
    | exact resolve eq1762 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761 eq1762
  have eq1768 : (σ x) = (k (σ (M.op x (M.op x y))) (σ x)) := by
    first
    | exact superpose eq1766 eq40
    | exact resolve eq40 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1766
  have eq1771 : (σ x) = (k (σ (M.op x (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq1768
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1768
    | exact resolve eq1768 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1768
  have eq1777 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (M.op (σ (M.op x (M.op x y))) (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1771 eq182
    | (have j0 := eq182 X0 (σ x) x
       grind)
    | exact resolve eq182 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1780 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (M.op (σ (M.op x (M.op x y))) (σ x)) (k X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1777 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq1777
    | exact resolve eq1777 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1777
  have eq1785 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (M.op (σ (M.op x (M.op x y))) (σ x)) (k X0 X0)) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1780 X0
       have i₂ := eq632 sF2
       grind)
    | exact superpose eq632 eq1780
    | (have j0 := eq1780 X0
       grind)
    | exact resolve eq1780 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq1923 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (k (σ (M.op x (M.op x y))) (σ x)) (k X0 X0)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1785 X0
       have i₂ := eq28 (σ (M.op x sF0)) sF2
       grind)
    | exact superpose eq28 eq1785
    | (have j1 := eq28 X0 (σ x)
       grind)
    | exact resolve eq1785 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1926 : (σ (M.op x (M.op x y))) = (M.op (M.op (σ (M.op x (M.op x y))) (σ x)) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1785 y
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq1785
    | exact resolve eq1785 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq1949 : ∀ X0 : G, (σ (M.op x (M.op x y))) = (M.op (k (σ (M.op x (M.op x y))) (σ x)) (k X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1923 X0
       have j1 := eq188 (σ x)
       grind)
    | (have r₁ := eq1923 X0
       have r₂ := eq188 (σ x)
       grind)
    | exact resolve eq1923 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq1955 : ∀ X0 : G, (M.op (σ x) (k X0 X0)) = (σ (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1771 eq1949
    | exact resolve eq1949 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq1959 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1365 eq1955
    | exact resolve eq1955 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365 eq1955
  have eq1961 : (M.op (σ x) (M.op (σ x) (σ y))) = (σ (M.op x (M.op x y))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1959
       have i₂ := eq632 sF2
       grind)
    | exact superpose eq632 eq1959
    | exact resolve eq1959 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959
  have eq2060 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1961 eq1926
    | exact resolve eq1926 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq2061 : (σ (M.op x (M.op x y))) = (M.op (k (σ (M.op x (M.op x y))) (σ x)) y) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1926
       have i₂ := eq28 (σ (M.op x sF0)) sF2
       grind)
    | exact superpose eq28 eq1926
    | (have j1 := eq28 x (σ x)
       grind)
    | exact resolve eq1926 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1926
  have eq2070 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) y) ∨ (σ x) = (k (σ x) (σ x)) := by grind
  clear eq2060
  have eq2079 : (σ (M.op x (M.op x y))) = (M.op (k (σ (M.op x (M.op x y))) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq188 (σ x)
       grind)
    | (have r₁ := eq2061
       have r₂ := eq188 (σ x)
       grind)
    | exact resolve eq2061 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq2061
  have eq2080 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1592 eq2070
    | exact resolve eq2070 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq2086 : (σ (M.op x (M.op x y))) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1771 eq2079
    | exact resolve eq2079 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771 eq2079
  have eq2091 : (σ (M.op x (M.op x y))) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2086
       have i₂ := eq632 sF2
       grind)
    | exact superpose eq632 eq2086
    | exact resolve eq2086 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086
  have eq2098 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) y) (M.op X0 X0)) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq2080 eq176
    | exact resolve eq176 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq2117 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) y) (k X0 X0)) ∨ (σ x) = (k (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2098 X0
       have i₂ := eq632 X0
       grind)
    | exact superpose eq632 eq2098
    | exact resolve eq2098 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq2177 : (σ x) = (M.op (M.op (σ x) y) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq685 eq2117
    | exact resolve eq2117 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117
  have eq4548 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq685 eq1363
    | exact resolve eq1363 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq5439 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1361 y X0 X1
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq1361
    | exact resolve eq1361 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5440 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (σ y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq685 eq1361
    | exact resolve eq1361 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq1361
  have eq5565 : ∀ X0 : G, (M.op (M.op X0 (k X0 X0)) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1385 X0 y
       have i₂ := eq675
       grind)
    | exact superpose eq675 eq1385
    | exact resolve eq1385 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq1385
  have eq6224 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq175 eq5439
    | exact resolve eq5439 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq6225 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) := by
    first
    | exact superpose eq176 eq5439
    | exact resolve eq5439 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq5439
  have eq6263 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq6224
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6224
    | exact resolve eq6224 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6224
  have eq6395 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6263 eq2091
    | exact resolve eq2091 eq6263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091 eq6263
  have eq6412 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq6395
    | exact resolve eq6395 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6395
  have eq6590 : (σ x) = (M.op (M.op (σ x) y) (σ x)) := by
    first
    | exact superpose eq6225 eq1592
    | exact resolve eq1592 eq6225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq6596 : (σ x) = (M.op (M.op (σ x) y) (σ y)) := by
    first
    | exact superpose eq6225 eq4548
    | exact resolve eq4548 eq6225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4548 eq6225
  have eq8162 : (M.op (σ x) y) = (M.op (M.op (M.op (σ x) y) (σ x)) (σ y)) := by
    first
    | exact superpose eq6596 eq5440
    | exact resolve eq5440 eq6596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6596
  have eq8163 : (M.op (σ x) y) = (M.op (M.op (M.op (σ x) y) (σ x)) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2177 eq5440
    | exact resolve eq5440 eq2177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177 eq5440
  have eq8307 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6590 eq8163
    | exact resolve eq8163 eq6590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8163
  have eq8308 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq6590 eq8162
    | exact resolve eq8162 eq6590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6590 eq8162
  have eq8376 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq8307
    | exact resolve eq8307 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8307
  have eq8377 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq26 eq8308
    | exact resolve eq8308 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8308
  have eq8410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6412 eq8376
    | exact resolve eq8376 eq6412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6412 eq8376
  have eq8417 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq8410
       have r₂ := eq27
       grind)
    | exact resolve eq8410 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8410
  have eq8648 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | exact superpose eq8417 eq142
    | exact resolve eq142 eq8417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq8684 : (σ x) = (M.op (M.op (σ x) (σ x)) y) := by
    first
    | exact superpose eq8417 eq5565
    | exact resolve eq5565 eq8417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8698 : (σ x) = (M.op (k (σ x) (σ x)) y) := by
    first
    | (have i₁ := eq8684
       have i₂ := eq632 sF2
       grind)
    | exact superpose eq632 eq8684
    | exact resolve eq8684 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8684
  have eq8714 : x = (k x x) := by
    first
    | exact superpose eq30 eq8648
    | exact resolve eq8648 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq8648
  have eq8719 : (σ x) = (M.op (σ x) y) := by
    first
    | exact superpose eq8417 eq8698
    | exact resolve eq8698 eq8417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8417 eq8698
  have eq8972 : x = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq5565 x
       have i₂ := eq8714
       grind)
    | exact superpose eq8714 eq5565
    | exact resolve eq5565 eq8714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5565
  have eq8991 : x = (M.op (k x x) y) := by
    first
    | (have i₁ := eq8972
       have i₂ := eq632 x
       grind)
    | exact superpose eq632 eq8972
    | exact resolve eq8972 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632 eq8972
  have eq9029 : x = (M.op x y) := by
    first
    | (have i₁ := eq8991
       have i₂ := eq8714
       grind)
    | exact superpose eq8714 eq8991
    | exact resolve eq8991 eq8714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8714 eq8991
  have eq9044 : x = (M.op x y) := by
    first
    | (have i₁ := eq9029
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9029
    | exact resolve eq9029 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq9029
  have eq9054 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9044
       grind)
    | exact superpose eq9044 eq22
    | exact resolve eq22 eq9044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9044
  have eq9139 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9054 eq20
    | exact resolve eq20 eq9054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9054
  have eq9218 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8719 eq8377
    | exact resolve eq8377 eq8719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8377 eq8719
  have eq9290 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq9218 eq27
    | exact resolve eq27 eq9218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9218
  have eq9346 : False := by grind
  exact eq9346
