import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_y_pyx_pxx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq20 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq20 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq122 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq112 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq112 X0 X1
       grind)
    | exact resolve eq13 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq137 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq122 (σ X1) (σ X0)
       grind)
    | exact superpose eq122 eq15
    | (have j1 := eq122 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq122 (τ X1) X0
       grind)
    | exact superpose eq122 eq17
    | (have j1 := eq122 (τ X1) X0
       grind)
    | exact resolve eq17 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq137 X0 X1
       have i₂ := eq122 X1 X0
       grind)
    | exact superpose eq122 eq137
    | (have j0 := eq137 X0 X1
       have j1 := eq122 (σ X1) (σ X0)
       grind)
    | exact resolve eq137 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq849 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq139
    | exact resolve eq139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq866 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq849 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq849
    | (have j0 := eq849 X0 X1
       grind)
    | exact resolve eq849 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq1042 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq145 x y
       grind)
    | exact superpose eq145 eq16
    | (have j1 := eq145 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 x y
       grind)
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq1081 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1042
  have eq1550 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1081
       grind)
    | exact superpose eq1081 eq16
    | exact resolve eq16 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1551 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq1081
       grind)
    | exact superpose eq1081 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1081
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1081
       grind)
    | exact resolve eq12 eq1081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081
  have eq1552 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1551
  have eq1554 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1552
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1552
    | exact resolve eq1552 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq4193 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq866 y x
       have i₂ := eq1554
       grind)
    | exact superpose eq1554 eq866
    | (have j0 := eq866 y x
       grind)
    | exact resolve eq866 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq4196 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq1554
       grind)
    | exact superpose eq1554 eq10
    | exact resolve eq10 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554
  have eq4215 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq4193
  have eq4223 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4196
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4196
    | exact resolve eq4196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196
  have eq4224 : x = (M.op x y) := by
    first
    | (have r₁ := eq4215
       have r₂ := eq1550
       grind)
    | exact resolve eq4215 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq4215
  have eq4227 : x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq4223
       have r₂ := eq12 y x
       grind)
    | exact resolve eq4223 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4223
  have eq8612 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq137 x y
       have i₂ := eq4227
       grind)
    | exact superpose eq4227 eq137
    | (have j0 := eq137 x y
       grind)
    | exact resolve eq137 eq4227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq4227
  have eq8619 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8612
  have eq12283 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8619
       grind)
    | exact superpose eq8619 eq16
    | exact resolve eq16 eq8619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8619
  have eq12287 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq12283
       have i₂ := eq4224
       grind)
    | exact superpose eq4224 eq12283
    | exact resolve eq12283 eq4224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4224 eq12283
  have eq12288 : False := by grind
  exact eq12288

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq36 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq36 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq36 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq45 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq60 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq61 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq53
  have eq63 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq61 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq61
  have eq160 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq164 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq160 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq160 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq160 X1 X1
       have r₂ := eq63 X1 X1
       grind)
    | exact resolve eq160 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq160
  have eq582 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq164 (σ X0) (σ X1)
       grind)
    | exact superpose eq164 eq15
    | exact resolve eq15 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq582 X0 X1
       have i₂ := eq164 X0 X1
       grind)
    | exact superpose eq164 eq582
    | exact resolve eq582 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq582
  have eq588 : False := by grind
  exact eq588

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
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
  have eq67 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq81 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99
    | exact resolve eq99 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq761 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq761
    | exact resolve eq761 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq765 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq762
       have r₂ := eq27
       grind)
    | exact resolve eq762 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq767 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq765
    | exact resolve eq765 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq769 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq767
    | exact resolve eq767 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq771 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq769 eq67
    | (have r₁ := eq67
       have r₂ := eq769
       grind)
    | exact resolve eq67 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq769
  have eq775 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq771
  have eq861 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq775
       have r₂ := eq774
       grind)
    | exact resolve eq775 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774 eq775
  have eq865 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq861 eq81
    | exact resolve eq81 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq873 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq865
    | exact resolve eq865 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq865
  have eq877 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq873
       have r₂ := eq66
       grind)
    | exact resolve eq873 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq922 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq877
       grind)
    | exact superpose eq877 eq74
    | exact resolve eq74 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq877
       grind)
    | exact superpose eq877 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq924 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq923
  have eq926 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq924
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq924
    | exact resolve eq924 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq927 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq926
  have eq928 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq922
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq922
    | exact resolve eq922 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq931 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq927
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq927
    | exact resolve eq927 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq934 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq931 eq51
    | (have r₁ := eq51
       have r₂ := eq931
       grind)
    | exact resolve eq51 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq936 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq934
  have eq987 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq928 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq988 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq987
  have eq992 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq988
    | exact resolve eq988 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq993 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq992
  have eq998 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq993
    | exact resolve eq993 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993
  have eq1003 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq998 eq27
    | exact resolve eq27 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1105 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq936 eq81
    | exact resolve eq81 eq936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq1116 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1105
    | exact resolve eq1105 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1119 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1116
       have r₂ := eq50
       grind)
    | exact resolve eq1116 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1125 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1119
       grind)
    | exact superpose eq1119 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1126 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1125
  have eq1128 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1126
    | exact resolve eq1126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1129 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1128
  have eq1133 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1129
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1129
    | exact resolve eq1129 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1129
  have eq1135 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1133 eq20
    | exact resolve eq20 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1138 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1133 eq66
    | (have r₁ := eq66
       have r₂ := eq1133
       grind)
    | exact resolve eq66 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1148 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq1133
  have eq1149 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq1138
  have eq1161 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1135
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1135
    | exact resolve eq1135 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1135
  have eq1224 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1161 eq1003
    | (have r₁ := eq1003
       have r₂ := eq1161
       grind)
    | exact resolve eq1003 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003 eq1161
  have eq1227 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1224
  have eq1228 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1227
  have eq1294 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1228 eq51
    | (have r₁ := eq51
       have r₂ := eq1228
       grind)
    | exact resolve eq51 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1228
  have eq1295 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1294
  have eq1375 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1295 eq81
    | exact resolve eq81 eq1295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq1295
  have eq1390 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1375
    | exact resolve eq1375 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1375
  have eq1393 : y = (k y x) := by
    first
    | (have r₁ := eq1390
       have r₂ := eq50
       grind)
    | exact resolve eq1390 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq1390
  have eq1447 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq1393
       grind)
    | exact superpose eq1393 eq74
    | exact resolve eq74 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq1452 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1447
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1447
    | exact resolve eq1447 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1447
  have eq1465 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1452 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1466 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1465
  have eq1468 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1466
    | exact resolve eq1466 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1471 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1468
    | exact resolve eq1468 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1468
  have eq1475 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1471 eq67
    | (have r₁ := eq67
       have r₂ := eq1471
       grind)
    | exact resolve eq67 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1478 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1471
  have eq1479 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1475
  have eq1480 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1452 eq1479
    | exact resolve eq1479 eq1452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq1479
  have eq1481 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1480
  have eq1591 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1481
       have r₂ := eq1478
       grind)
    | exact resolve eq1481 eq1478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478 eq1481
  have eq1595 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1591 eq27
    | exact resolve eq27 eq1591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1591
  have eq3507 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1149
       have r₂ := eq1148
       grind)
    | exact resolve eq1149 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq3508 : x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3507
       have i₂ := eq1393
       grind)
    | exact superpose eq1393 eq3507
    | exact resolve eq3507 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393 eq3507
  have eq3509 : x = (M.op x y) := by
    first
    | (have r₁ := eq3508
       have r₂ := eq1148
       grind)
    | exact resolve eq3508 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148 eq3508
  have eq3511 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3509 eq20
    | exact resolve eq20 eq3509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3509
  have eq3538 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3511
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3511
    | exact resolve eq3511 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3511
  have eq3540 : False := by grind
  exact eq3540

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_x_pxy_y_pxy_Equation2132 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
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
  clear eq25 eq36
  have eq50 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    grind
  have eq89 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq109 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq108
    | exact resolve eq108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq265 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq379 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X0 X0) X1 x
       have i₂ := eq14 (M.op X0 X0) X0 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq406 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 ∨ (k X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq379 X0 X1
       grind)
    | (have i₁ := eq12 X1 X2
       have i₂ := eq379 X1 X0
       grind)
    | exact superpose eq379 eq12
    | (have j0 := eq12 X1 X2
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq379 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq379 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X0
       have i₂ := eq379 X0 (σ X0)
       grind)
    | (have i₁ := eq89 X0 X0
       have i₂ := eq379 (σ X0) X1
       grind)
    | exact superpose eq379 eq89
    | exact resolve eq89 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq520 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq493 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq538 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq265
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq12413 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq520 X0 (τ X1)
       grind)
    | exact superpose eq520 eq35
    | (have j1 := eq520 X0 (τ X1)
       grind)
    | exact resolve eq35 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq12414 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq520 X0 x
       grind)
    | exact superpose eq520 eq44
    | (have j1 := eq520 X0 x
       grind)
    | exact resolve eq44 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq12499 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12414 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq12414
    | (have j0 := eq12414 X0
       grind)
    | exact resolve eq12414 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12414
  have eq12500 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12413 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12413
    | (have j0 := eq12413 X0 X1
       grind)
    | exact resolve eq12413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12413
  have eq12522 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12500 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq12500
    | (have j0 := eq12500 X0 X1
       grind)
    | exact resolve eq12500 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12500
  have eq12835 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq379 X1 X0
       have i₂ := eq12499 X0
       grind)
    | exact superpose eq12499 eq379
    | (have j1 := eq12499 X1
       grind)
    | exact resolve eq379 eq12499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12499
  have eq13149 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12522 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12522
  have eq13223 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13149 X1 (τ X0)
       have i₂ := eq538 X0 X0
       grind)
    | exact superpose eq538 eq13149
    | (have j0 := eq13149 X1 (τ X0)
       grind)
    | exact resolve eq13149 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq13609 : ∀ X0 X1 : G, (k x x) = (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq12835 eq50
    | (have j1 := eq12835 X1 X1
       grind)
    | exact resolve eq50 eq12835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq12835
  have eq18807 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq18808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18807
    | exact resolve eq18807 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18807
  have eq18819 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18808
       have r₂ := eq28
       grind)
    | exact resolve eq18808 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18808
  have eq18821 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq18819
       have i₂ := eq379 X0 sF3
       grind)
    | (have i₁ := eq18819
       have i₂ := eq379 sF3 x
       grind)
    | exact superpose eq379 eq18819
    | exact resolve eq18819 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq18819
  have eq18930 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq18821 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18821
  have eq18931 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq18930
  have eq19016 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq18931 eq13609
    | (have j0 := eq13609 X0 X0
       grind)
    | exact resolve eq13609 eq18931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13609 eq18931
  have eq19021 : ∀ X0 : G, x = (k x x) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq19016
    | (have j0 := eq19016 X0
       grind)
    | exact resolve eq19016 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19016
  have eq19026 : ∀ X0 : G, x = (k x x) ∨ (M.op X0 X0) = (σ x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq19021 X0
       have j1 := eq406 X0 x x
       grind)
    | (have r₁ := eq19021 X0
       have r₂ := eq406 X0 (σ x) x
       grind)
    | (have r₁ := eq19021 X0
       have r₂ := eq406 x x x
       grind)
    | (have r₁ := eq19021 X0
       have r₂ := eq406 y x x
       grind)
    | exact resolve eq19021 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq19021
  have eq19027 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq19026 X0
       have j1 := eq13149 x x
       grind)
    | (have r₁ := eq19026 X0
       have r₂ := eq13149 X0 x
       grind)
    | exact resolve eq19026 eq13149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19026
  have eq19033 : ∀ X0 : G, (k x x) = (M.op x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    grind
  have eq19228 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq19033 X0
       grind)
    | exact superpose eq19033 eq44
    | (have j1 := eq19033 X0
       grind)
    | exact resolve eq44 eq19033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq19033
  have eq21342 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq19228 X0
       have i₂ := eq19027 X1
       grind)
    | exact superpose eq19027 eq19228
    | (have j0 := eq19228 X0
       have j1 := eq19027 X0
       grind)
    | exact resolve eq19228 eq19027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19027 eq19228
  have eq21450 : ∀ X0 X1 : G, (σ x) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq21342 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21342
    | (have j0 := eq21342 X0 X0
       grind)
    | exact resolve eq21342 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21342
  have eq21452 : ∀ X0 X1 : G, (M.op X1 X1) = (σ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq21450 X1 X1
       have j1 := eq13149 X1 (σ x)
       grind)
    | (have r₁ := eq21450 X0 X1
       have r₂ := eq13149 X0 (σ x)
       grind)
    | exact resolve eq21450 eq13149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13149 eq21450
  have eq21574 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq21452 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21452
  have eq21575 : ∀ X0 : G, (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq21574 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21574
  have eq21622 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    grind
  have eq21626 : (k (σ x) (M.op (σ x) (σ x))) = (M.op (σ x) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq21575 x
       grind)
    | exact superpose eq21575 eq63
    | exact resolve eq63 eq21575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq21775 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21626
       have i₂ := eq21575 sF2
       grind)
    | exact superpose eq21575 eq21626
    | exact resolve eq21626 eq21575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21626
  have eq21825 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq21775
       have i₂ := eq21575 sF2
       grind)
    | exact superpose eq21575 eq21775
    | exact resolve eq21775 eq21575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21775
  have eq21889 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq21825 eq13223
    | (have j0 := eq13223 (σ x) X0
       grind)
    | exact resolve eq13223 eq21825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13223 eq21825
  have eq21892 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) := by
    intro X0
    first
    | (have j0 := eq21889 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21889
  have eq21908 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | exact superpose eq29 eq21892
    | exact resolve eq21892 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq21892
  have eq21929 : x = (σ x) := by
    first
    | (have i₁ := eq21908 x
       have i₂ := eq21575 x
       grind)
    | exact superpose eq21575 eq21908
    | exact resolve eq21908 eq21575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21575 eq21908
  have eq21938 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq21929 eq27
    | exact resolve eq27 eq21929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq22258 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq21929 eq21622
    | exact resolve eq21622 eq21929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21622
  have eq22338 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq22258 y
       grind)
    | exact superpose eq22258 eq45
    | exact resolve eq45 eq22258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq22376 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq21929 eq22338
    | exact resolve eq22338 eq21929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21929 eq22338
  have eq22455 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq22376
       have i₂ := eq22258 sF3
       grind)
    | exact superpose eq22258 eq22376
    | exact resolve eq22376 eq22258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22258 eq22376
  have eq22524 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21938 eq22455
    | exact resolve eq22455 eq21938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21938 eq22455
  have eq22570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22524
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq22524
    | exact resolve eq22524 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq22524
  have eq22603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq22570
    | exact resolve eq22570 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22570
  have eq22624 : False := by grind
  exact eq22624

/-- `Equation2132`: `x = ((y ◇ y) ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pyy_Equation2132 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) Law2132 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2132.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq25 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X0 X0) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X1) (M.op X0 X0) X2
       have i₂ := eq9 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 x
       have i₂ := eq25 (M.op X0 X0) X1 x
       grind)
    | (have i₁ := eq9 (M.op X1 X1) X1 (M.op X1 X1)
       have i₂ := eq25 X0 (M.op (M.op X1 X1) (M.op X1 X1)) x
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq153 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq144 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq144 X0 X1
       grind)
    | exact resolve eq13 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq153 (σ X1) (σ X0)
       grind)
    | exact superpose eq153 eq15
    | (have j1 := eq153 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq168 X0 X1
       have i₂ := eq153 X1 X0
       grind)
    | exact superpose eq153 eq168
    | (have j0 := eq168 X0 X1
       have j1 := eq153 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq168 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq168
  have eq300 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq144 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq144 (σ X1) X0
       grind)
    | exact superpose eq144 eq22
    | exact resolve eq22 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq144
  have eq1631 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq170 x y
       grind)
    | exact superpose eq170 eq16
    | (have j1 := eq170 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq170 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq170 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq170 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq1637 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1631
  have eq3531 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1637
       grind)
    | exact superpose eq1637 eq10
    | exact resolve eq10 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1637
  have eq3555 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3531
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3531
    | exact resolve eq3531 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3531
  have eq3556 : x = y := by grind
  clear eq3555
  have eq5855 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3556
       grind)
    | exact superpose eq3556 eq16
    | exact resolve eq16 eq3556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3556
  have eq5856 : False := by grind
  exact eq5856

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) X1)) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    grind
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq82
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq83
    | exact resolve eq83 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq91
    | exact resolve eq91 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq227 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq16
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq53 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq53 X2 X3 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 X2
       have i₂ := eq343 X0 X2
       grind)
    | (have i₁ := eq14 X2 X1 X2
       have i₂ := eq343 X2 X0
       grind)
    | exact superpose eq343 eq14
    | exact resolve eq14 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X1) X1 X2
       have i₂ := eq343 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq53 (M.op X1 X1) X1 X2
       have i₂ := eq343 (M.op X1 X1) X0
       grind)
    | exact superpose eq343 eq53
    | exact resolve eq53 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq53 X2 X3 X0
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op x y)) = (M.op (M.op (M.op X1 X1) x) (M.op (M.op X2 X2) y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X1 X1) (σ x)) (M.op (M.op X2 X2) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 X3))) X1) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X2 x X3 X4
       have i₂ := eq56 X1 X0 (M.op X2 X3) x
       grind)
    | (have i₁ := eq56 X0 (M.op (M.op X0 X2) (M.op X0 X2)) X2 X3
       have i₂ := eq56 (M.op X0 X2) (M.op X0 X2) (M.op X0 X2) X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 X4 x X2
       have i₂ := eq56 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq56 X2 X2 X2 x
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X4) = (M.op (M.op (M.op X3 X3) X2) (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X4 X4) X3 X2
       have i₂ := eq56 X1 X0 X2 X4
       grind)
    | (have i₁ := eq14 (M.op (M.op X1 X1) (M.op X0 X2)) X1 X0
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq501 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq227 X0 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq227
    | (have j0 := eq227 X0 x
       grind)
    | exact resolve eq227 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq53 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq53 eq66
    | exact resolve eq66 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq66
  have eq679 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X0
       have i₂ := eq343 X0 (σ X0)
       grind)
    | (have i₁ := eq76 X0 X0
       have i₂ := eq343 (σ X0) X1
       grind)
    | exact superpose eq343 eq76
    | exact resolve eq76 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq708 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq679 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq4345 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op (M.op X2 X2) (M.op x y)) (M.op (M.op (M.op X0 X0) x) (M.op (M.op X1 X1) y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq432 eq14
    | exact resolve eq14 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq4427 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op (M.op X2 X2) (M.op (σ x) (σ y))) (M.op (M.op (M.op X0 X0) (σ x)) (M.op (M.op X1 X1) (σ y)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq433 eq14
    | exact resolve eq14 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq5327 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X2 (M.op (M.op X0 X2) (M.op X3 X3)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq427 X2 X1 (M.op X0 X2) X3 x
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq427
    | exact resolve eq427 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5332 : ∀ X0 X1 : G, x = (M.op (M.op X0 X0) (M.op y (M.op (M.op x y) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq54 eq427
    | exact resolve eq427 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5357 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq345 X1 x X2 x
       have i₂ := eq427 X1 x X2 x X0
       grind)
    | exact superpose eq427 eq345
    | exact resolve eq345 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq5838 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5357 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq345 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq345 eq5357
    | exact resolve eq5357 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq6656 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq28 eq5838
    | (have j0 := eq5838 (σ x) X0 (σ y)
       grind)
    | exact resolve eq5838 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23218 : ∀ X1 X2 : G, (M.op (M.op x X2) (M.op y (M.op (M.op x y) (M.op X1 X1)))) = X2 := by
    intro X1 X2
    first
    | exact superpose eq5332 eq5357
    | exact resolve eq5357 eq5332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5332
  have eq24699 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X1)
       have i₂ := eq708 X0 (τ X1)
       grind)
    | exact superpose eq708 eq36
    | (have j1 := eq708 X0 (τ X1)
       grind)
    | exact resolve eq36 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24701 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq74
       have i₂ := eq708 X0 y
       grind)
    | exact superpose eq708 eq74
    | (have j1 := eq708 X0 y
       grind)
    | exact resolve eq74 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24761 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq708 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq24790 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq24701 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq24701
    | (have j0 := eq24701 X0
       grind)
    | exact resolve eq24701 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24701
  have eq24792 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24699 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq24699
    | (have j0 := eq24699 X0 X1
       grind)
    | exact resolve eq24699 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24699
  have eq24854 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24792 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq24792
    | (have j0 := eq24792 X0 X1
       grind)
    | exact resolve eq24792 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24792
  have eq26706 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq24854 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34975 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq92 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq34975
    | exact resolve eq34975 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34975
  have eq34987 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq34976
       have r₂ := eq29
       grind)
    | exact resolve eq34976 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34976
  have eq34989 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq34987
       have i₂ := eq343 X0 sF2
       grind)
    | (have i₁ := eq34987
       have i₂ := eq343 sF2 x
       grind)
    | exact superpose eq343 eq34987
    | exact resolve eq34987 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34987
  have eq35125 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    grind
  clear eq34989
  have eq35247 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq28 eq35125
    | (have j0 := eq35125 X0
       grind)
    | exact resolve eq35125 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35125
  have eq36680 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq35247 eq92
    | (have j1 := eq35247 X0
       grind)
    | exact resolve eq92 eq35247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq35247
  have eq36690 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq36680 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36680
  have eq36692 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq36690 X0
       grind)
    | (have r₁ := eq36690 X0
       have r₂ := eq29
       grind)
    | exact resolve eq36690 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36690
  have eq36694 : ∀ X0 X1 : G, x = (M.op y y) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq36692 X1
       have i₂ := eq343 X0 x
       grind)
    | (have i₁ := eq36692 X1
       have i₂ := eq343 x X0
       grind)
    | exact superpose eq343 eq36692
    | (have j0 := eq36692 X1
       grind)
    | exact resolve eq36692 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36754 : ∀ X0 X1 : G, (k y X0) = (M.op y X0) ∨ x = (M.op y y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 x
       have i₂ := eq36692 X0
       grind)
    | exact superpose eq36692 eq552
    | (have j1 := eq36692 X1
       grind)
    | exact resolve eq552 eq36692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36828 : ∀ X0 X1 X2 : G, (σ y) = (M.op X2 X2) ∨ (M.op X1 X1) = y ∨ (M.op X0 X0) = x := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36694 X1 X2
       have i₂ := eq343 X0 y
       grind)
    | (have i₁ := eq36694 X1 X2
       have i₂ := eq343 y X0
       grind)
    | exact superpose eq343 eq36694
    | (have j0 := eq36694 X1 X2
       grind)
    | exact resolve eq36694 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36694
  have eq37735 : ∀ X1 X2 X3 : G, (σ y) = (k X1 X1) ∨ (σ y) = X1 ∨ y = (M.op X2 X2) ∨ x = (M.op X3 X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq24854 X2 X1
       have i₂ := eq36828 x X1 X2
       grind)
    | (have i₁ := eq24854 X1 X1
       have i₂ := eq36828 x X1 X2
       grind)
    | exact superpose eq36828 eq24854
    | (have j0 := eq24854 X2 y
       have j1 := eq36828 X3 X2 X2
       grind)
    | exact resolve eq24854 eq36828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37862 : ∀ X0 X1 : G, y ≠ (σ y) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have j0 := eq36828 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37863 : ∀ X0 X1 : G, x ≠ (σ y) ∨ (M.op X1 X1) = y ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | (have j0 := eq36828 X0 X1 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36828
  have eq38132 : ∀ X0 : G, (k (σ y) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq74
       have i₂ := eq36754 y X0
       grind)
    | exact superpose eq36754 eq74
    | (have j1 := eq36754 X0 X0
       grind)
    | exact resolve eq74 eq36754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq36754
  have eq47166 : ∀ X0 X1 : G, (k (σ y) (σ y)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = x ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq38132 X0
       have i₂ := eq343 X0 y
       grind)
    | (have i₁ := eq38132 X0
       have i₂ := eq343 y X1
       grind)
    | exact superpose eq343 eq38132
    | (have j0 := eq38132 X1
       grind)
    | exact resolve eq38132 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38132
  have eq48210 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (σ (σ y)) ∨ x = (σ y) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq45
       have i₂ := eq37735 x X0 X1
       grind)
    | exact superpose eq37735 eq45
    | (have j1 := eq37735 x X0 X1
       grind)
    | exact resolve eq45 eq37735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq37735
  have eq48316 : ∀ X0 X1 : G, (k (σ x) (σ x)) = (σ (σ y)) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have j0 := eq48210 X0 X1
       have j1 := eq37863 X1 X0
       grind)
    | (have r₁ := eq48210 X0 X1
       have r₂ := eq37863 X0 X1
       grind)
    | exact resolve eq48210 eq37863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37863 eq48210
  have eq48532 : ∀ X0 X1 : G, (k x x) = (τ (σ (σ y))) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | exact superpose eq48316 eq51
    | (have j1 := eq48316 X0 X1
       grind)
    | exact resolve eq51 eq48316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48316
  have eq48582 : ∀ X0 X1 : G, (σ y) = (k x x) ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq48532 X0 X1
       have i₂ := eq16 sF3
       grind)
    | exact superpose eq16 eq48532
    | (have j0 := eq48532 X0 X1
       grind)
    | exact resolve eq48532 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48532
  have eq49287 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ x = (M.op y y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq47166 x X1
       have i₂ := eq36692 X0
       grind)
    | exact superpose eq36692 eq47166
    | (have j0 := eq47166 y X0
       have j1 := eq36692 X0
       grind)
    | exact resolve eq47166 eq36692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36692 eq47166
  have eq49423 : ∀ X0 X1 : G, (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ x = (M.op y y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq49287 X0 X1
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq49287
    | (have j0 := eq49287 X0 X0
       grind)
    | exact resolve eq49287 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49287
  have eq49438 : ∀ X0 X1 : G, x = (M.op y y) ∨ (M.op X0 X0) = (σ y) ∨ x = y ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq49423 X0 X0
       have j1 := eq26706 y x
       grind)
    | (have r₁ := eq49423 X0 X1
       have r₂ := eq26706 X0 (σ y)
       grind)
    | exact resolve eq49423 eq26706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26706 eq49423
  have eq52344 : ∀ X0 X1 X2 : G, (σ y) = (M.op X2 X2) ∨ (M.op X1 X1) = (σ y) ∨ x = y ∨ (M.op X0 X0) = x := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49438 X2 X1
       have i₂ := eq343 X0 y
       grind)
    | (have i₁ := eq49438 X2 X1
       have i₂ := eq343 y X0
       grind)
    | exact superpose eq343 eq49438
    | (have j0 := eq49438 X2 X2
       grind)
    | exact resolve eq49438 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49438
  have eq53562 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ x = y ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have j0 := eq52344 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52344
  have eq53564 : ∀ X0 X1 : G, (M.op X1 X1) = x ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X1
    first
    | (have j0 := eq53562 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53562
  have eq53690 : ∀ X0 X1 : G, (k x X0) = (M.op x X0) ∨ x = y ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    grind
  have eq53829 : ∀ X1 : G, x = (k (σ y) (σ y)) ∨ x = (σ y) ∨ x = y ∨ (M.op X1 X1) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq24790 X1
       have i₂ := eq53564 x X1
       grind)
    | exact superpose eq53564 eq24790
    | (have j0 := eq24790 X1
       have j1 := eq53564 X1 X1
       grind)
    | exact resolve eq24790 eq53564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24790
  have eq53993 : ∀ X0 : G, (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq105
       have i₂ := eq53564 X0 y
       grind)
    | exact superpose eq53564 eq105
    | (have j1 := eq53564 X0 x
       grind)
    | exact resolve eq105 eq53564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq54005 : ∀ X0 : G, x ≠ (σ y) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq53564 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53564
  have eq54006 : ∀ X0 : G, (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq53993 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53993
  have eq54019 : ∀ X0 : G, (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq54006 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq54006
    | (have j0 := eq54006 X0
       grind)
    | exact resolve eq54006 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54006
  have eq54357 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq46
       have i₂ := eq53690 y X0
       grind)
    | exact superpose eq53690 eq46
    | (have j1 := eq53690 X0 X0
       grind)
    | exact resolve eq46 eq53690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53690
  have eq54387 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq54357 X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq54357
    | (have j0 := eq54357 X0
       grind)
    | exact resolve eq54357 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54357
  have eq54425 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq22 eq54387
    | (have j0 := eq54387 X0
       grind)
    | exact resolve eq54387 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54387
  have eq55152 : ∀ X1 : G, x = (k (σ y) (σ y)) ∨ x = y ∨ (M.op X1 X1) = (σ y) := by
    intro X1
    first
    | (have j0 := eq53829 X1
       have j1 := eq54005 X1
       grind)
    | (have r₁ := eq53829 X1
       have r₂ := eq54005 x
       grind)
    | exact resolve eq53829 eq54005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53829 eq54005
  have eq55191 : ∀ X0 X1 : G, x = (σ x) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ x = y ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq55152 eq54019
    | (have j0 := eq54019 X0
       have j1 := eq55152 X0
       grind)
    | exact resolve eq54019 eq55152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54019 eq55152
  have eq55217 : ∀ X0 X1 : G, (M.op X1 X1) = (σ y) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ x = (σ x) := by
    intro X0 X1
    first
    | (have j0 := eq55191 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55191
  have eq59180 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq55217 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55217
  have eq59181 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = y ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq59180 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59180
  have eq59318 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = y ∨ x = (σ x) := by
    intro X0
    grind
  have eq59320 : x = (M.op (M.op (σ y) y) (M.op x y)) ∨ x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq59181 x
       grind)
    | exact superpose eq59181 eq54
    | exact resolve eq54 eq59181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq59321 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq59181 x
       grind)
    | exact superpose eq59181 eq55
    | exact resolve eq55 eq59181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59462 : ∀ X1 : G, (σ y) = (k X1 X1) ∨ (σ y) = X1 ∨ x = y ∨ x = (σ x) := by
    intro X1
    first
    | (have i₁ := eq24854 x X1
       have i₂ := eq59181 x
       grind)
    | exact superpose eq59181 eq24854
    | exact resolve eq24854 eq59181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24854
  have eq59822 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq59318 eq104
    | exact resolve eq104 eq59318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq59895 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq59321
       have i₂ := eq59181 sF3
       grind)
    | exact superpose eq59181 eq59321
    | exact resolve eq59321 eq59181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59321
  have eq59939 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (σ x) := by grind
  clear eq59895
  have eq59969 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X1 X1)))) ∨ x = y ∨ x = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq59939 eq5327
    | exact resolve eq5327 eq59939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59939
  have eq59971 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ y)) ∨ x = y ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq6656 eq59969
    | exact resolve eq59969 eq6656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59969
  have eq60610 : ∀ X1 : G, (σ y) = (M.op (σ y) (M.op X1 X1)) ∨ x = y ∨ x = (σ x) := by
    intro X1
    first
    | exact superpose eq59971 eq359
    | exact resolve eq359 eq59971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60628 : ∀ X1 : G, (M.op (M.op (σ y) X1) (σ y)) = X1 ∨ x = y ∨ x = (σ x) := by
    intro X1
    first
    | exact superpose eq59971 eq5357
    | exact resolve eq5357 eq59971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59971
  have eq61781 : (τ (σ y)) = (k y y) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq59822
       have i₂ := eq59181 sF3
       grind)
    | exact superpose eq59181 eq59822
    | exact resolve eq59822 eq59181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59181 eq59822
  have eq61845 : (τ (σ y)) = (k y y) ∨ x = y ∨ x = (σ x) := by grind
  clear eq61781
  have eq61881 : y = (k y y) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq31 eq61845
    | exact resolve eq61845 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61845
  have eq61944 : y = (σ y) ∨ y = (σ y) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq59462 y
       have i₂ := eq61881
       grind)
    | exact superpose eq61881 eq59462
    | (have j0 := eq59462 y
       grind)
    | exact resolve eq59462 eq61881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59462
  have eq61947 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq61881
       grind)
    | exact superpose eq61881 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq61881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61881
  have eq61948 : y = (M.op y y) ∨ x = y ∨ x = (σ x) := by grind
  clear eq61947
  have eq61951 : y = (σ y) ∨ x = y ∨ x = (σ x) := by grind
  clear eq61944
  have eq62127 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq61951 eq59318
    | exact resolve eq59318 eq61951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62150 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = y ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq62127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62127
  have eq62403 : (σ y) = (M.op (σ y) y) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq60610 y
       have i₂ := eq61948
       grind)
    | exact superpose eq61948 eq60610
    | exact resolve eq60610 eq61948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60610 eq61948
  have eq62421 : (σ y) = (M.op (σ y) y) ∨ x = y ∨ x = (σ x) := by grind
  clear eq62403
  have eq63132 : x = (M.op (σ y) (M.op x y)) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq62421 eq59320
    | exact resolve eq59320 eq62421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59320 eq62421
  have eq63158 : x = (M.op (σ y) (M.op x y)) ∨ x = y ∨ x = (σ x) := by grind
  clear eq63132
  have eq63246 : x = (M.op y (M.op x y)) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq61951 eq63158
    | exact resolve eq63158 eq61951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61951 eq63158
  have eq63268 : x = (M.op y (M.op x y)) ∨ x = y ∨ x = (σ x) := by grind
  clear eq63246
  have eq65600 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq62150 sF0
       grind)
    | exact superpose eq62150 eq75
    | exact resolve eq75 eq62150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62150
  have eq108360 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq63268 eq65600
    | exact resolve eq65600 eq63268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63268 eq65600
  have eq108433 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = (σ x) := by grind
  clear eq108360
  have eq108437 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = (σ x) := by
    first
    | (have i₁ := eq108433
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq108433
    | exact resolve eq108433 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108433
  have eq108769 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq108437 eq59318
    | exact resolve eq59318 eq108437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59318 eq108437
  have eq108774 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y ∨ x = (σ x) := by grind
  clear eq108769
  have eq108796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (σ x) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq108774 eq60628
    | exact resolve eq60628 eq108774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60628 eq108774
  have eq108818 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (σ x) := by grind
  clear eq108796
  have eq108824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (σ x) := by
    first
    | exact superpose eq28 eq108818
    | exact resolve eq108818 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108818
  have eq108826 : x = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq108824
       have r₂ := eq29
       grind)
    | exact resolve eq108824 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108824
  have eq108827 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | exact superpose eq108826 eq28
    | exact resolve eq28 eq108826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108829 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq108826 eq37
    | exact resolve eq37 eq108826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq108830 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq108826 eq41
    | exact resolve eq41 eq108826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq108833 : (k x x) = (τ (k x x)) ∨ x = y := by
    first
    | exact superpose eq108826 eq51
    | exact resolve eq51 eq108826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq108908 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op x (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq108826 eq6656
    | exact resolve eq6656 eq108826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108934 : ∀ X0 : G, (σ (M.op x y)) = (k x (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq108826 eq54425
    | (have j0 := eq54425 X0
       grind)
    | exact resolve eq54425 eq108826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108826
  have eq108935 : ∀ X0 : G, (σ (M.op x y)) = (k x (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq108934 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108934
  have eq109334 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op y (M.op (M.op x y) (M.op X0 X0)))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq108827 eq23218
    | exact resolve eq23218 eq108827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23218
  have eq111056 : ∀ X0 X1 : G, (σ y) = (τ (σ y)) ∨ x = y ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | (have i₁ := eq108833
       have i₂ := eq48582 X0 X1
       grind)
    | exact superpose eq48582 eq108833
    | (have j1 := eq48582 X0 X1
       grind)
    | exact resolve eq108833 eq48582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48582 eq108833
  have eq111159 : ∀ X0 X1 : G, y = (σ y) ∨ x = y ∨ (M.op X0 X0) = y ∨ (M.op X1 X1) = x := by
    intro X0 X1
    first
    | exact superpose eq31 eq111056
    | (have j0 := eq111056 X0 X1
       grind)
    | exact resolve eq111056 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111056
  have eq111161 : ∀ X0 X1 : G, (M.op X1 X1) = x ∨ (M.op X0 X0) = y ∨ x = y := by
    intro X0 X1
    first
    | (have j0 := eq111159 X0 X1
       have j1 := eq37862 X0 X1
       grind)
    | (have r₁ := eq111159 X0 X1
       have r₂ := eq37862 X0 X1
       grind)
    | exact resolve eq111159 eq37862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37862 eq111159
  have eq114551 : ∀ X0 : G, (k x X0) = (σ (k x (τ X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq108829 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq108829
    | exact resolve eq108829 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114671 : ∀ X0 : G, (τ (σ (k x X0))) = (k (τ x) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq227 x X0
       have i₂ := eq108829 X0
       grind)
    | exact superpose eq108829 eq227
    | exact resolve eq227 eq108829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq108829
  have eq114707 : ∀ X0 : G, (k x X0) = (k (τ x) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq114671 X0
       have i₂ := eq16 (k x X0)
       grind)
    | exact superpose eq16 eq114671
    | exact resolve eq114671 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114671
  have eq114732 : ∀ X0 : G, (k x X0) = (k (σ x) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq114551 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq114551
    | exact resolve eq114551 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114551
  have eq115135 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq114732 eq40
    | exact resolve eq40 eq114732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq115244 : ∀ X0 : G, (k (σ x) X0) = (k (σ (σ x)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq115135 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq115135
    | exact resolve eq115135 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115135
  have eq115554 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (σ x) (τ X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq115244 eq328
    | exact resolve eq328 eq115244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328 eq115244
  have eq117056 : ∀ X0 : G, (k X0 x) = (σ (k (τ X0) x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq108830 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq108830
    | exact resolve eq108830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108830
  have eq117260 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq117056 X0
       have i₂ := eq36 X0 x
       grind)
    | exact superpose eq36 eq117056
    | exact resolve eq117056 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq117056
  have eq117282 : ∀ X0 : G, (k X0 x) = (k X0 (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq117260 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq117260
    | (have j0 := eq117260 X0
       grind)
    | exact resolve eq117260 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117260
  have eq117737 : (k x (σ x)) = (k (τ x) x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq117282 eq114707
    | exact resolve eq114707 eq117282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114707 eq117282
  have eq117811 : (k x (σ x)) = (k (τ x) x) ∨ x = y := by grind
  clear eq117737
  have eq117904 : (k x (σ x)) = (τ (k x (σ x))) ∨ x = y := by
    first
    | (have i₁ := eq117811
       have i₂ := eq501 x
       grind)
    | exact superpose eq501 eq117811
    | exact resolve eq117811 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq117811
  have eq122442 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) (M.op X2 (M.op x (M.op X1 X1)))) = X2 ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq108908 eq445
    | exact resolve eq445 eq108908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq122444 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X1) (M.op x (M.op X2 X2))) (M.op (M.op (M.op X3 X3) (σ y)) (M.op (σ x) (σ y)))) ∨ x = y := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq108908 eq457
    | exact resolve eq457 eq108908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457 eq108908
  have eq122487 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X1) (M.op x (M.op X2 X2))) (σ x)) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq55 eq122444
    | exact resolve eq122444 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122444
  have eq122489 : ∀ X1 X2 : G, (M.op (σ x) (M.op X2 (M.op x (M.op X1 X1)))) = X2 ∨ x = y := by
    intro X1 X2
    first
    | exact superpose eq55 eq122442
    | exact resolve eq122442 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122442
  have eq122517 : ∀ X0 : G, (M.op X0 X0) = (M.op x (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq122487 X0 x x
       have i₂ := eq360 x x x
       grind)
    | exact superpose eq360 eq122487
    | exact resolve eq122487 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122487
  have eq122616 : ∀ X1 X2 : G, (M.op (M.op (M.op x (σ x)) X1) (M.op X2 X1)) = X2 ∨ x = y := by
    intro X1 X2
    first
    | (have i₁ := eq14 X2 x X1
       have i₂ := eq122517 x
       grind)
    | exact superpose eq122517 eq14
    | exact resolve eq14 eq122517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149897 : ∀ X1 : G, x = (M.op x (σ x)) ∨ x = y ∨ (M.op X1 X1) = y ∨ x = y := by
    intro X1
    first
    | (have i₁ := eq122517 x
       have i₂ := eq111161 X1 x
       grind)
    | exact superpose eq111161 eq122517
    | (have j1 := eq111161 X1 X1
       grind)
    | exact resolve eq122517 eq111161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111161 eq122517
  have eq150166 : ∀ X1 : G, x = (M.op x (σ x)) ∨ x = y ∨ (M.op X1 X1) = y := by
    intro X1
    first
    | (have j0 := eq149897 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149897
  have eq212956 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op x y) (M.op X1 X1))) = (M.op (M.op (M.op (M.op X2 X2) (σ y)) (M.op (σ x) (σ y))) y) ∨ x = y := by
    intro X0 X1 X2
    first
    | exact superpose eq109334 eq439
    | exact resolve eq439 eq109334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq109334
  have eq213026 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op x y) (M.op X1 X1))) = (M.op (σ x) y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq55 eq212956
    | exact resolve eq212956 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212956
  have eq213050 : (M.op x y) = (M.op (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq213026 x x
       have i₂ := eq360 x x sF0
       grind)
    | exact superpose eq360 eq213026
    | exact resolve eq213026 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq213026
  have eq213087 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (σ x) (M.op X0 X0))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq213050 eq5838
    | exact resolve eq5838 eq213050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230365 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq122489 x (M.op x X0)
       have i₂ := eq5838 x x X0
       grind)
    | exact superpose eq5838 eq122489
    | exact resolve eq122489 eq5838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5838 eq122489
  have eq242842 : x = (M.op (M.op (M.op x (σ x)) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq108827 eq122616
    | exact resolve eq122616 eq108827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq242925 : (σ x) = (M.op (M.op (M.op x (σ x)) y) (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq213050 eq122616
    | exact resolve eq122616 eq213050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122616 eq213050
  have eq243554 : (σ x) = (M.op (M.op (M.op x (σ x)) y) (M.op x y)) ∨ x = y := by grind
  clear eq242925
  have eq243624 : x = (M.op (M.op (M.op x (σ x)) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq242842
  have eq243797 : ∀ X0 : G, (σ x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = y ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq150166 eq243554
    | (have j1 := eq150166 X0
       grind)
    | exact resolve eq243554 eq150166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150166 eq243554
  have eq243839 : ∀ X0 : G, (σ x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq243797 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243797
  have eq243844 : ∀ X0 : G, (σ x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq243839 X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq243839
    | (have j0 := eq243839 X0
       grind)
    | exact resolve eq243839 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243839
  have eq243898 : ∀ X0 X1 : G, (M.op X1 X1) = y ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq243844 X0
       have i₂ := eq343 X0 sF0
       grind)
    | (have i₁ := eq243844 X0
       have i₂ := eq343 sF0 X1
       grind)
    | exact superpose eq343 eq243844
    | (have j0 := eq243844 X1
       grind)
    | exact resolve eq243844 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243844
  have eq244848 : ∀ X0 : G, (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq89
       have i₂ := eq243898 X0 x
       grind)
    | exact superpose eq243898 eq89
    | (have j1 := eq243898 X0 x
       grind)
    | exact resolve eq89 eq243898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq243898
  have eq244916 : ∀ X0 : G, (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq244848 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244848
  have eq245018 : ∀ X0 : G, (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq244916 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq244916
    | (have j0 := eq244916 X0
       grind)
    | exact resolve eq244916 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244916
  have eq256214 : ∀ X0 : G, (σ y) = (k x (σ x)) ∨ x = y ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq245018 eq114732
    | (have j1 := eq245018 X0
       grind)
    | exact resolve eq114732 eq245018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245018
  have eq256258 : ∀ X0 : G, (σ y) = (k x (σ x)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq256214 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256214
  have eq268446 : ∀ X0 : G, (σ y) = (τ (σ y)) ∨ x = y ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | exact superpose eq256258 eq117904
    | (have j1 := eq256258 X0
       grind)
    | exact resolve eq117904 eq256258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117904 eq256258
  have eq268521 : ∀ X0 : G, (σ y) = (τ (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have j0 := eq268446 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268446
  have eq268549 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = y ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq31 eq268521
    | (have j0 := eq268521 X0
       grind)
    | exact resolve eq268521 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268521
  have eq268673 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ x = y ∨ y = (σ y) := by
    intro X0
    grind
  have eq290607 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ x = y ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq268673 eq54425
    | (have j0 := eq54425 X0
       grind)
    | exact resolve eq54425 eq268673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54425 eq268673
  have eq290618 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq290607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290607
  have eq290798 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq28 eq290618
    | (have j0 := eq290618 X0
       grind)
    | exact resolve eq290618 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290618
  have eq290846 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = y ∨ y = (σ y) := by
    intro X0
    first
    | (have j0 := eq290798 X0
       grind)
    | (have r₁ := eq290798 X0
       have r₂ := eq29
       grind)
    | exact resolve eq290798 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290798
  have eq291316 : (σ x) = (σ y) ∨ x = y ∨ y = (σ y) ∨ x = y ∨ y = (σ y) := by
    first
    | (have i₁ := eq268549 x
       have i₂ := eq290846 x
       grind)
    | exact superpose eq290846 eq268549
    | exact resolve eq268549 eq290846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268549 eq290846
  have eq291698 : (σ x) = (σ y) ∨ x = y ∨ y = (σ y) := by grind
  clear eq291316
  have eq295450 : y = (τ (σ x)) ∨ x = y ∨ y = (σ y) := by
    first
    | exact superpose eq291698 eq31
    | exact resolve eq31 eq291698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291698
  have eq296114 : x = y ∨ x = y ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq295450
    | exact resolve eq295450 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq295450
  have eq296115 : y = (σ y) ∨ x = y := by grind
  clear eq296114
  have eq296118 : y = (τ y) ∨ x = y := by
    first
    | exact superpose eq296115 eq31
    | exact resolve eq31 eq296115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq296426 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq296115 eq108827
    | exact resolve eq108827 eq296115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108827
  have eq296495 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq296426
  have eq296680 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq296495
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq296495
    | exact resolve eq296495 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296495
  have eq296683 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq296680 eq29
    | exact resolve eq29 eq296680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296839 : (σ (k x y)) = (k (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq296118
       grind)
    | exact superpose eq296118 eq44
    | exact resolve eq44 eq296118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq297055 : (k (σ x) y) = (τ (k (σ x) y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq115554 y
       have i₂ := eq296118
       grind)
    | exact superpose eq296118 eq115554
    | exact resolve eq115554 eq296118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115554 eq296118
  have eq297058 : (k (σ x) y) = (τ (k (σ x) y)) ∨ x = y := by grind
  clear eq297055
  have eq297097 : (k (σ x) (σ y)) = (k (σ x) y) ∨ x = y := by
    first
    | (have i₁ := eq296839
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq296839
    | exact resolve eq296839 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq296839
  have eq297392 : (k x (σ y)) = (k (σ x) y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq297097 eq114732
    | exact resolve eq114732 eq297097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114732 eq297097
  have eq297412 : (k x (σ y)) = (k (σ x) y) ∨ x = y := by grind
  clear eq297392
  have eq303581 : (k x (σ y)) = (τ (k x (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq297412 eq297058
    | exact resolve eq297058 eq297412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297058 eq297412
  have eq303822 : (k x (σ y)) = (τ (k x (σ y))) ∨ x = y := by grind
  clear eq303581
  have eq304946 : ∀ X0 : G, (σ (M.op x y)) = (τ (σ (M.op x y))) ∨ x = y ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq108935 eq303822
    | (have j1 := eq108935 X0
       grind)
    | exact resolve eq303822 eq108935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108935 eq303822
  have eq305180 : ∀ X0 : G, (σ (M.op x y)) = (τ (σ (M.op x y))) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq304946 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304946
  have eq305187 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ x = y ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq32 eq305180
    | (have j0 := eq305180 X0
       grind)
    | exact resolve eq305180 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq305180
  have eq305188 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq305187 X0
       grind)
    | (have r₁ := eq305187 X0
       have r₂ := eq296683
       grind)
    | exact resolve eq305187 eq296683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296683 eq305187
  have eq305325 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) ∨ x = y := by
    intro X0
    grind
  have eq305328 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq305188 x
       grind)
    | exact superpose eq305188 eq55
    | exact resolve eq55 eq305188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq305627 : y = (M.op (M.op x y) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq213087 x
       have i₂ := eq305188 x
       grind)
    | exact superpose eq305188 eq213087
    | exact resolve eq213087 eq305188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213087
  have eq305944 : (σ y) = (M.op x (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq230365 sF2
       have i₂ := eq305188 sF2
       grind)
    | exact superpose eq305188 eq230365
    | exact resolve eq230365 eq305188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230365
  have eq305976 : (σ y) = (M.op x (σ x)) ∨ x = y := by grind
  clear eq305944
  have eq306026 : y = (M.op (M.op x y) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq305627
  have eq306176 : y = (M.op (M.op x y) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq28 eq306026
    | exact resolve eq306026 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306026
  have eq306251 : x = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq305976 eq243624
    | exact resolve eq243624 eq305976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243624 eq305976
  have eq306314 : x = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq306251
  have eq310722 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq296680 eq306176
    | exact resolve eq306176 eq296680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306176
  have eq310762 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq310722
  have eq312823 : ∀ X0 : G, (M.op X0 X0) = y ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq310762
       have i₂ := eq343 X0 sF0
       grind)
    | (have i₁ := eq310762
       have i₂ := eq343 sF0 x
       grind)
    | exact superpose eq343 eq310762
    | exact resolve eq310762 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq310762
  have eq337132 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq296115 eq305325
    | exact resolve eq305325 eq296115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296115
  have eq337687 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq337132 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337132
  have eq337823 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq305328
       have i₂ := eq305188 sF3
       grind)
    | exact superpose eq305188 eq305328
    | exact resolve eq305328 eq305188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305188 eq305328
  have eq337899 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq337823
  have eq337986 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X1 X1)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq337899 eq5327
    | exact resolve eq5327 eq337899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5327 eq337899
  have eq338004 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq6656 eq337986
    | exact resolve eq337986 eq6656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6656 eq337986
  have eq349975 : x = (M.op y (M.op (σ x) (σ y))) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq306314
       have i₂ := eq312823 sF3
       grind)
    | exact superpose eq312823 eq306314
    | exact resolve eq306314 eq312823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306314 eq312823
  have eq350076 : x = (M.op y (M.op (σ x) (σ y))) ∨ x = y := by grind
  clear eq349975
  have eq350195 : x = (M.op y (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq296680 eq350076
    | exact resolve eq350076 eq296680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296680 eq350076
  have eq350253 : x = (M.op y (M.op x y)) ∨ x = y := by grind
  clear eq350195
  have eq375114 : (k (σ y) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq75
       have i₂ := eq337687 sF0
       grind)
    | exact superpose eq337687 eq75
    | exact resolve eq75 eq337687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq337687
  have eq395437 : ∀ X1 : G, (M.op (M.op (σ y) X1) (σ y)) = X1 ∨ x = y := by
    intro X1
    first
    | exact superpose eq338004 eq5357
    | exact resolve eq5357 eq338004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5357 eq338004
  have eq1039906 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq350253 eq375114
    | exact resolve eq375114 eq350253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350253 eq375114
  have eq1040042 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq1039906
  have eq1040046 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq1040042
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1040042
    | exact resolve eq1040042 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040042
  have eq1040072 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1040046 eq305325
    | exact resolve eq305325 eq1040046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305325 eq1040046
  have eq1040080 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq1040072
  have eq1040119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1040080 eq395437
    | exact resolve eq395437 eq1040080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395437 eq1040080
  have eq1040206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1040119
  have eq1040220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq1040206
    | exact resolve eq1040206 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1040206
  have eq1040222 : x = y := by
    first
    | (have r₁ := eq1040220
       have r₂ := eq29
       grind)
    | exact resolve eq1040220 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040220
  have eq1040223 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq1040222
       grind)
    | exact superpose eq1040222 eq20
    | exact resolve eq20 eq1040222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1040224 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq1040222
       grind)
    | exact superpose eq1040222 eq26
    | exact resolve eq26 eq1040222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1040408 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X1) (M.op x y)) (M.op (M.op (M.op X2 X2) x) (M.op (M.op X3 X3) x))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4345 X2 X3 X1 X0
       have i₂ := eq1040222
       grind)
    | exact superpose eq1040222 eq4345
    | exact resolve eq4345 eq1040222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4345 eq1040222
  have eq1040460 : ∀ X0 X1 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X1) (M.op x y)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1040408 X0 X1 x X3
       have i₂ := eq14 (M.op X3 X3) x x
       grind)
    | exact superpose eq14 eq1040408
    | exact resolve eq1040408 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040408
  have eq1040616 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1040224
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1040224
    | exact resolve eq1040224 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1040224
  have eq1040617 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1040460 X0 x X0
       have i₂ := eq359 X0 x sF0
       grind)
    | exact superpose eq359 eq1040460
    | exact resolve eq1040460 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040460
  have eq1041504 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq552 X0 x
       have i₂ := eq1040223
       grind)
    | exact superpose eq1040223 eq552
    | exact resolve eq552 eq1040223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq1040223
  have eq1043215 : ∀ X1 X2 X3 : G, (M.op x y) = (M.op (M.op (M.op X1 X1) (M.op (σ x) (σ y))) (M.op (M.op (M.op X2 X2) (σ x)) (M.op (M.op X3 X3) (σ y)))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq4427 X2 X3 X1 x
       have i₂ := eq1040617 x
       grind)
    | exact superpose eq1040617 eq4427
    | exact resolve eq4427 eq1040617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4427
  have eq1045559 : ∀ X1 X2 X3 : G, (M.op x y) = (M.op (M.op (M.op X1 X1) (M.op (σ x) (σ y))) (M.op (M.op (M.op X2 X2) (σ x)) (M.op (M.op X3 X3) (σ x)))) := by
    intro X1 X2 X3
    first
    | exact superpose eq1040616 eq1043215
    | exact resolve eq1043215 eq1040616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040616 eq1043215
  have eq1046803 : ∀ X1 X3 : G, (M.op x y) = (M.op (M.op (M.op X1 X1) (M.op (σ x) (σ y))) (M.op X3 X3)) := by
    intro X1 X3
    first
    | (have i₁ := eq1045559 X1 X1 X3
       have i₂ := eq14 (M.op X3 X3) X1 sF2
       grind)
    | exact superpose eq14 eq1045559
    | exact resolve eq1045559 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045559
  have eq1047513 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1046803 x x
       have i₂ := eq359 x x sF4
       grind)
    | exact superpose eq359 eq1046803
    | exact resolve eq1046803 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq1046803
  have eq1048028 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1047513 eq29
    | exact resolve eq29 eq1047513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1047513
  have eq1086247 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1041504 eq24761
    | (have j0 := eq24761 X0 (M.op x y)
       grind)
    | exact resolve eq24761 eq1041504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24761 eq1041504
  have eq1086729 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1086247 X0
       have i₂ := eq1040617 sF0
       grind)
    | exact superpose eq1040617 eq1086247
    | (have j0 := eq1086247 X0
       grind)
    | exact resolve eq1086247 eq1040617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086247
  have eq1086730 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq1086729 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1086729
  have eq1086897 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22 eq1086730
    | (have j0 := eq1086730 X0
       grind)
    | exact resolve eq1086730 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1086730
  have eq1086998 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq1086897 x
       have i₂ := eq1040617 x
       grind)
    | exact superpose eq1040617 eq1086897
    | exact resolve eq1086897 eq1040617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040617 eq1086897
  have eq1087048 : False := by grind
  exact eq1087048

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pxy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 (M.op X1 X0) X1
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
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq178 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k (M.op X0 X0) X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X0 X1
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq176
    | exact resolve eq176 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq181
  have eq647 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (k (M.op X0 X0) X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq573 X1 X2
       have i₂ := eq540 X0 X1
       grind)
    | (have i₁ := eq573 X1 X2
       have i₂ := eq540 X1 X0
       grind)
    | exact superpose eq540 eq573
    | exact resolve eq573 eq540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq1497 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
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
  clear eq18
  have eq1498 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28
  have eq1593 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1598 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1593 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1593 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq1593 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | (have r₁ := eq1593 x
       have r₂ := eq13 (k x x) x
       grind)
    | exact resolve eq1593 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1706 : ∀ X0 : G, x = (M.op (M.op (k X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq1598 X0
       grind)
    | exact superpose eq1598 eq177
    | exact resolve eq177 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1707 : ∀ X0 : G, (σ x) = (M.op (M.op (k X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq1598 X0
       grind)
    | exact superpose eq1598 eq178
    | exact resolve eq178 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1710 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1
       have i₂ := eq1598 X0
       grind)
    | exact superpose eq1598 eq540
    | exact resolve eq540 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq1849 : ∀ X0 X1 : G, (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1598 X0
       have i₂ := eq1710 X1 X0
       grind)
    | exact superpose eq1710 eq1598
    | exact resolve eq1598 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710
  have eq3792 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1497
       grind)
    | exact superpose eq1497 eq40
    | exact resolve eq40 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3793 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3792
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3792
    | exact resolve eq3792 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3792
  have eq3795 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq3793
    | exact resolve eq3793 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3793
  have eq3797 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq3795
       have i₂ := eq1598 x
       grind)
    | exact superpose eq1598 eq3795
    | exact resolve eq3795 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3795
  have eq3808 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq3797 eq1498
    | exact resolve eq1498 eq3797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3797
  have eq3815 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq3808
       have r₂ := eq27
       grind)
    | exact resolve eq3808 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3808
  have eq3819 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq3815
       have i₂ := eq1598 sF2
       grind)
    | exact superpose eq1598 eq3815
    | exact resolve eq3815 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3815
  have eq3827 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq3819 eq1707
    | exact resolve eq1707 eq3819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq3829 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq3819 eq1849
    | exact resolve eq1849 eq3819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3819
  have eq4195 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op (σ x) (σ y)))) = X1 ∨ (M.op x y) = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 (M.op X0 X0) X1
       have i₂ := eq3829 (M.op X0 X0)
       grind)
    | exact superpose eq3829 eq647
    | exact resolve eq647 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4221 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (M.op (σ x) (σ y)))) = X1 ∨ (M.op x y) = (k x x) := by
    intro X0 X1
    first
    | (have i₁ := eq4195 X0 X1
       have i₂ := eq1598 X0
       grind)
    | exact superpose eq1598 eq4195
    | exact resolve eq4195 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4195
  have eq4260 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (σ y)))) = X1 ∨ (M.op x y) = (k x x) := by
    intro X1
    first
    | exact superpose eq3829 eq4221
    | exact resolve eq4221 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4221
  have eq8350 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (M.op X2 X2) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    intro X0 X1 X2
    first
    | exact superpose eq4260 eq179
    | exact resolve eq179 eq4260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8358 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (k X2 X2) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8350 X0 X1 X2
       have i₂ := eq1598 X2
       grind)
    | exact superpose eq1598 eq8350
    | exact resolve eq8350 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8350
  have eq8386 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (k X2 X2) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8358 X0 X1 X2
       have i₂ := eq1598 X1
       grind)
    | exact superpose eq1598 eq8358
    | exact resolve eq8358 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8358
  have eq8412 : ∀ X0 X1 : G, (M.op (k X1 X1) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    intro X0 X1
    first
    | exact superpose eq3829 eq8386
    | exact resolve eq8386 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8386
  have eq8424 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq3829 eq8412
    | exact resolve eq8412 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3829 eq8412
  have eq8426 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = X0 ∨ (M.op x y) = (k x x) := by
    intro X0
    first
    | exact superpose eq4260 eq8424
    | exact resolve eq8424 eq4260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4260 eq8424
  have eq9809 : (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | exact superpose eq8426 eq3827
    | exact resolve eq3827 eq8426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3827 eq8426
  have eq9819 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) := by grind
  clear eq9809
  have eq9911 : x = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1706 x
       have i₂ := eq9819
       grind)
    | exact superpose eq9819 eq1706
    | exact resolve eq1706 eq9819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq9914 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1849 x X0
       have i₂ := eq9819
       grind)
    | exact superpose eq9819 eq1849
    | exact resolve eq1849 eq9819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849 eq9819
  have eq10160 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op x y))) = X1 ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 (M.op X0 X0) X1
       have i₂ := eq9914 (M.op X0 X0)
       grind)
    | exact superpose eq9914 eq647
    | exact resolve eq647 eq9914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq10192 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X1 (M.op x y))) = X1 ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq10160 X0 X1
       have i₂ := eq1598 X0
       grind)
    | exact superpose eq1598 eq10160
    | exact resolve eq10160 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10160
  have eq10237 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = X1 ∨ (σ x) = (σ y) := by
    intro X1
    first
    | exact superpose eq9914 eq10192
    | exact resolve eq10192 eq9914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10192
  have eq13001 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op x y))) = (M.op (M.op (M.op X2 X2) X0) (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | exact superpose eq10237 eq179
    | exact resolve eq179 eq10237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq13009 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op x y))) = (M.op (M.op (k X2 X2) X0) (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13001 X0 X1 X2
       have i₂ := eq1598 X2
       grind)
    | exact superpose eq1598 eq13001
    | exact resolve eq13001 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13001
  have eq13039 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) (M.op X0 (M.op x y))) = (M.op (M.op (k X2 X2) X0) (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13009 X0 X1 X2
       have i₂ := eq1598 X1
       grind)
    | exact superpose eq1598 eq13009
    | exact resolve eq13009 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13009
  have eq13066 : ∀ X0 X1 : G, (M.op (k X1 X1) (M.op X0 (M.op x y))) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq9914 eq13039
    | exact resolve eq13039 eq9914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13039
  have eq13079 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq9914 eq13066
    | exact resolve eq13066 eq9914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9914 eq13066
  have eq13082 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq10237 eq13079
    | exact resolve eq13079 eq10237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10237 eq13079
  have eq13185 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13082 eq9911
    | exact resolve eq9911 eq13082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9911 eq13082
  have eq13201 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq13185
  have eq13292 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq13201 eq32
    | exact resolve eq32 eq13201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq13201
  have eq13323 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq13292
    | exact resolve eq13292 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13292
  have eq13324 : x = y := by grind
  clear eq13323
  have eq13328 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq13324
       grind)
    | exact superpose eq13324 eq24
    | exact resolve eq24 eq13324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq13332 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1497
       have i₂ := eq13324
       grind)
    | exact superpose eq13324 eq1497
    | exact resolve eq1497 eq13324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497 eq13324
  have eq13346 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13332
       have i₂ := eq1598 x
       grind)
    | exact superpose eq1598 eq13332
    | exact resolve eq13332 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13332
  have eq13347 : (M.op x y) = (k x x) := by grind
  clear eq13346
  have eq13351 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq13328
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13328
    | exact resolve eq13328 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13328
  have eq13366 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq13351 eq1498
    | exact resolve eq1498 eq13351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498 eq13351
  have eq13374 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq13366
       have i₂ := eq1598 sF2
       grind)
    | exact superpose eq1598 eq13366
    | exact resolve eq13366 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598 eq13366
  have eq13375 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq13374
  have eq13960 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq13347
       grind)
    | exact superpose eq13347 eq40
    | exact resolve eq40 eq13347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq13347
  have eq14008 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq13960
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13960
    | exact resolve eq13960 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13960
  have eq14023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13375 eq14008
    | exact resolve eq14008 eq13375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13375 eq14008
  have eq14028 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14023
    | exact resolve eq14023 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14023
  have eq14030 : False := by grind
  exact eq14030

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq37 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
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
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq57 : ∀ X0 X1 X2 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq37 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq68 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq151 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq799 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq800 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq799 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq805 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq800 X0 X1
       have j1 := eq151 X0 X1
       grind)
    | (have r₁ := eq800 X0 X1
       have r₂ := eq151 X0 X1
       grind)
    | (have r₁ := eq800 X1 X1
       have r₂ := eq151 X1 X1
       grind)
    | exact resolve eq800 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq800
  have eq1152 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq805 (σ X0) (σ X1)
       grind)
    | exact superpose eq805 eq15
    | exact resolve eq15 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1155 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1152 X0 X1
       have i₂ := eq805 X0 X1
       grind)
    | exact superpose eq805 eq1152
    | exact resolve eq1152 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805 eq1152
  have eq1159 : False := by grind
  exact eq1159
