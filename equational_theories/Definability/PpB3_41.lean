import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then X else if m(Y,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_x_x_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
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
  clear eq18
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq64 X0 X1
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq76 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op (σ X0) X1) X0
       have i₂ := eq72 (σ X0) X1
       grind)
    | exact superpose eq72 eq23
    | exact resolve eq23 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq72
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4138 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq88 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq88
    | (have j0 := eq88 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq88 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4139 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ (M.op (M.op (M.op X0 X1) X2) X2))) ∨ (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq66 X0 X1 X2
       grind)
    | exact superpose eq66 eq88
    | (have j0 := eq88 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       grind)
    | exact resolve eq88 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq88
  have eq4260 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ (M.op (M.op (M.op X0 X1) X2) X2))) ∨ (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4139 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq26884 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ (M.op (M.op (M.op X0 X1) X2) X2))
       have i₂ := eq4260 X0 X1 X2
       grind)
    | exact superpose eq4260 eq64
    | (have j1 := eq4260 X0 X1 X2
       grind)
    | exact resolve eq64 eq4260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4260
  have eq26977 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq26884 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26884
  have eq27128 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq26977 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq26977
    | exact resolve eq26977 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26977
  have eq34237 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4138 x y
       grind)
    | exact superpose eq4138 eq16
    | (have j1 := eq4138 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq4138 x y
       grind)
    | exact resolve eq16 eq4138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4138
  have eq34428 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq34237
  have eq69791 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76 x (σ y)
       have i₂ := eq34428
       grind)
    | exact superpose eq34428 eq76
    | exact resolve eq76 eq34428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34428
  have eq70014 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq69791
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq69791
    | exact resolve eq69791 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69791
  have eq70030 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq70014
       have r₂ := eq12 y x
       grind)
    | exact resolve eq70014 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70014
  have eq70054 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq76 x (σ x)
       have i₂ := eq70030
       grind)
    | exact superpose eq70030 eq76
    | exact resolve eq76 eq70030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq70030
  have eq70321 : y = (k y x) ∨ y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70054
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq70054
    | exact resolve eq70054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70054
  have eq70322 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq70321
  have eq70366 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70322
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq70322
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq70322 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70322
  have eq70371 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq70366
  have eq70712 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq70371
  have eq70825 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq27128 x y
       have i₂ := eq70712
       grind)
    | exact superpose eq70712 eq27128
    | exact resolve eq27128 eq70712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70890 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70825
       grind)
    | exact superpose eq70825 eq16
    | exact resolve eq16 eq70825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70825
  have eq71115 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq70712 eq70890
    | exact resolve eq70890 eq70712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70712 eq70890
  have eq71116 : y = (M.op x x) := by grind
  clear eq71115
  have eq71168 : y = (M.op x y) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq71116
       grind)
    | exact superpose eq71116 eq64
    | exact resolve eq64 eq71116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq71116
  have eq71337 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71168
       grind)
    | exact superpose eq71168 eq16
    | exact resolve eq16 eq71168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71449 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27128 x y
       have i₂ := eq71168
       grind)
    | exact superpose eq71168 eq27128
    | exact resolve eq27128 eq71168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27128 eq71168
  have eq71531 : False := by grind
  exact eq71531

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq24 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
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
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq34 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq39 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq40 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq46
  have eq54 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq41 X1 X0
       grind)
    | (have r₁ := eq50 X1 X0
       have r₂ := eq41 X0 X1
       grind)
    | (have r₁ := eq50 X0 (M.op X1 X1)
       have r₂ := eq41 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq50 X1 X1
       have r₂ := eq41 (k X1 X1) X1
       grind)
    | exact resolve eq50 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq50
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq112 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq116 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq112 X0 X1
       have j1 := eq56 X1 X0
       grind)
    | (have r₁ := eq112 X1 X0
       have r₂ := eq56 X0 X1
       grind)
    | (have r₁ := eq112 X0 X0
       have r₂ := eq56 X0 X0
       grind)
    | exact resolve eq112 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq112
  have eq188 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq116 (σ X1) (σ X0)
       grind)
    | exact superpose eq116 eq15
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq116 X1 X0
       grind)
    | exact superpose eq116 eq188
    | exact resolve eq188 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq188
  have eq195 : False := by grind
  exact eq195

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq315 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq339 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq315 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq340 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq339 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq346 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq340 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq340 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq340 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq354 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq346 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq346
    | (have j0 := eq346 X0 X1
       grind)
    | exact resolve eq346 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq355 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq360 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq355 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq355
    | exact resolve eq355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq355 x y
       grind)
    | exact superpose eq355 eq16
    | exact resolve eq16 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq448 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq360 X0 (τ X1)
       grind)
    | exact superpose eq360 eq17
    | exact resolve eq17 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq360
  have eq466 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq448 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq448
    | exact resolve eq448 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448
  have eq474 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq466 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq466
    | exact resolve eq466 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq486 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq372
       have i₂ := eq474 x y
       grind)
    | exact superpose eq474 eq372
    | exact resolve eq372 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq474
  have eq487 : False := by grind
  exact eq487

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_x_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq74 X0 X1
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq74 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq74
  have eq80 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (k (σ (M.op (τ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) X1)
       have i₂ := eq76 (τ X0) X1
       grind)
    | exact superpose eq76 eq18
    | exact resolve eq18 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq81 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) X1) X0
       have i₂ := eq76 (σ X0) X1
       grind)
    | exact superpose eq76 eq22
    | exact resolve eq22 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq76
  have eq649 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq649 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq649
    | (have j0 := eq649 (σ X0) (σ X1)
       grind)
    | exact resolve eq649 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq684 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ (M.op (τ X0) X1))) ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq80 X0 X1
       have i₂ := eq649 (σ (M.op (τ X0) X1)) X0
       grind)
    | exact superpose eq649 eq80
    | (have j1 := eq649 (σ (M.op (τ X0) X1)) X0
       grind)
    | exact resolve eq80 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq693 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq649 (τ (M.op (σ X0) X1)) X0
       grind)
    | exact superpose eq649 eq81
    | (have j1 := eq649 (τ (M.op (σ X0) X1)) X0
       grind)
    | exact resolve eq81 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq698 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq693 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq699 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have j0 := eq684 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq811 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq699 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq699
    | exact resolve eq699 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq1302 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq658 X1 X0
       have i₂ := eq649 X1 X0
       grind)
    | exact superpose eq649 eq658
    | (have j0 := eq658 X1 X0
       have j1 := eq649 (σ X1) (σ X0)
       grind)
    | exact resolve eq658 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq658
  have eq17417 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1302 x y
       grind)
    | exact superpose eq1302 eq16
    | (have j1 := eq1302 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1302 x y
       grind)
    | exact resolve eq16 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq17578 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq17417
  have eq17673 : (τ (σ y)) = (M.op x (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq698 x (σ y)
       have i₂ := eq17578
       grind)
    | exact superpose eq17578 eq698
    | exact resolve eq698 eq17578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq17578
  have eq17779 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq17673
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq17673
    | exact resolve eq17673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17673
  have eq17780 : y = (M.op x y) := by grind
  clear eq17779
  have eq17798 : y = (M.op x y) := by grind
  clear eq17780
  have eq17813 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17798
       grind)
    | exact superpose eq17798 eq16
    | exact resolve eq16 eq17798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17839 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq811 x y
       have i₂ := eq17798
       grind)
    | exact superpose eq17798 eq811
    | exact resolve eq811 eq17798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq17798
  have eq17872 : False := by grind
  exact eq17872

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyy_x_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X2) X2 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X2) X2) = X0 ∨ (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 ∨ (M.op (M.op (M.op X0 X1) X2) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq72 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq319 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq14
    | (have j0 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq14 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq382 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op (M.op (M.op (M.op X0 X1) X2) X3) X3)) ∨ (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75 (M.op X0 X0) (M.op (M.op X0 X1) X2) X2
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq75
    | exact resolve eq75 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq75
  have eq2619 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq319 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq319
    | (have j0 := eq319 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq319 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2650 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq319 X1 X0
       grind)
    | exact superpose eq319 eq10
    | (have j1 := eq319 X1 X0
       grind)
    | exact resolve eq10 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2651 : ∀ X0 X1 X2 : G, (σ (k (k X1 X0) X2)) = (k (M.op (σ X0) (σ X1)) (σ X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X1 X0) X2
       have i₂ := eq319 X1 X0
       grind)
    | exact superpose eq319 eq15
    | (have j1 := eq319 X1 X0
       grind)
    | exact resolve eq15 eq319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33483 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq320 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq33785 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33483 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq33483
    | (have j0 := eq33483 (σ X1) (σ X0)
       grind)
    | exact resolve eq33483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33483
  have eq33853 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33785 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq33785
    | (have j0 := eq33785 X0 X1
       grind)
    | exact resolve eq33785 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33785
  have eq33885 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33853 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq33853
    | (have j0 := eq33853 X0 X1
       grind)
    | exact resolve eq33853 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33853
  have eq33908 : ∀ X0 X1 : G, (M.op (τ (σ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33885 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33885
    | (have j0 := eq33885 X0 X1
       grind)
    | exact resolve eq33885 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33885
  have eq33930 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq33908 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq33908
    | (have j0 := eq33908 X0 X1
       grind)
    | exact resolve eq33908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33908
  have eq33949 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33930 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33930
    | (have j0 := eq33930 X0 X1
       grind)
    | exact resolve eq33930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33930
  have eq33963 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33949 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33949
    | (have j0 := eq33949 X0 X1
       grind)
    | exact resolve eq33949 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33949
  have eq33993 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33963 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq33963
    | (have j0 := eq33963 (σ X0) (σ X1)
       grind)
    | exact resolve eq33963 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33963
  have eq34159 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq382 X0 x X0 X0
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq382
    | exact resolve eq382 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq34211 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq34159 X0
       have j1 := eq69 X0 X0
       grind)
    | (have r₁ := eq34159 x
       have r₂ := eq69 x x
       grind)
    | exact resolve eq34159 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq34159
  have eq34222 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq34211 (σ X0)
       grind)
    | exact superpose eq34211 eq22
    | exact resolve eq22 eq34211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq34291 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34222 x
       have i₂ := eq2650 x x
       grind)
    | exact superpose eq2650 eq34222
    | (have j1 := eq2650 X0 X0
       grind)
    | exact resolve eq34222 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2650 eq34222
  have eq34390 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq34291 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34291
  have eq36890 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq34211 (σ X0)
       have i₂ := eq2651 X0 X0 X0
       grind)
    | exact superpose eq2651 eq34211
    | (have j1 := eq2651 X0 X0 x
       grind)
    | exact resolve eq34211 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651 eq34211
  have eq36913 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq36890 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36890
  have eq36935 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq34390 eq36913
    | (have j0 := eq36913 X0
       have j1 := eq34390 X0
       grind)
    | exact resolve eq36913 eq34390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34390 eq36913
  have eq37017 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq36935 (τ X0)
       grind)
    | exact superpose eq36935 eq18
    | (have j1 := eq36935 (τ X0)
       grind)
    | exact resolve eq18 eq36935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq36935
  have eq37107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37017 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37017
    | (have j0 := eq37017 X0
       grind)
    | exact resolve eq37017 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37017
  have eq37136 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq37107 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37107
    | (have j0 := eq37107 X0
       grind)
    | exact resolve eq37107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37107
  have eq37165 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq37136 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq37136 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq37136 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37136
  have eq37272 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37165 (σ X0)
       grind)
    | exact superpose eq37165 eq15
    | exact resolve eq15 eq37165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37412 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37272 X0
       have i₂ := eq37165 X0
       grind)
    | exact superpose eq37165 eq37272
    | exact resolve eq37272 eq37165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37165 eq37272
  have eq48260 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2619 x y
       grind)
    | exact superpose eq2619 eq16
    | (have j1 := eq2619 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2619 x y
       grind)
    | exact resolve eq16 eq2619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq48448 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq48260
  have eq79295 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48448
       grind)
    | exact superpose eq48448 eq16
    | exact resolve eq16 eq48448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79316 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74 (σ x) (σ y)
       have i₂ := eq48448
       grind)
    | exact superpose eq48448 eq74
    | (have j0 := eq74 (σ x) (σ y)
       grind)
    | exact resolve eq74 eq48448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79401 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq48448
  have eq79441 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79316
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq79316
    | exact resolve eq79316 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79316
  have eq79458 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14 eq79441
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq79441 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79441
  have eq79465 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq79295 eq79401 eq79458
  have eq79475 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79465
       grind)
    | exact superpose eq79465 eq16
    | exact resolve eq16 eq79465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79486 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq79465
       grind)
    | exact superpose eq79465 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq79465
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq79465
       grind)
    | exact resolve eq12 eq79465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79490 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63 (σ x) (σ y)
       have i₂ := eq79465
       grind)
    | exact superpose eq79465 eq63
    | exact resolve eq63 eq79465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79465
  have eq79579 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq79486
  have eq79630 : (σ x) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79490
       have i₂ := eq37412 x
       grind)
    | exact superpose eq37412 eq79490
    | exact resolve eq79490 eq37412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79490
  have eq79633 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79579
       have i₂ := eq37412 x
       grind)
    | exact superpose eq37412 eq79579
    | exact resolve eq79579 eq37412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79579
  have eq79646 : (σ (M.op x x)) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79633
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq79633
    | exact resolve eq79633 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79633
  have eq79649 : (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14 eq79646
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq79646 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79646
  have eq79685 : (M.op x x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq79630
       grind)
    | exact superpose eq79630 eq10
    | exact resolve eq10 eq79630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79630
  have eq79862 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79685
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq79685
    | exact resolve eq79685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79685
  have eq80024 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79862 eq79649
    | exact resolve eq79649 eq79862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79649 eq79862
  have eq80025 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq80024
       have r₂ := eq79475
       grind)
    | exact resolve eq80024 eq79475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79475 eq80024
  have eq80036 : y = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74 x y
       have i₂ := eq80025
       grind)
    | exact superpose eq80025 eq74
    | (have j0 := eq74 x y
       grind)
    | exact resolve eq74 eq80025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80121 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq80123 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq80036
       have r₂ := eq80121
       grind)
    | exact resolve eq80036 eq80121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80036 eq80121
  have eq80129 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq319 y x
       have i₂ := eq80123
       grind)
    | exact superpose eq80123 eq319
    | (have j0 := eq319 y x
       grind)
    | exact resolve eq319 eq80123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq80146 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq80129
  have eq84763 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq80146
       grind)
    | exact superpose eq80146 eq16
    | exact resolve eq16 eq80146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80146
  have eq84922 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80025 eq84763
    | exact resolve eq84763 eq80025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84763
  have eq84923 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq84922
  have eq84957 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84923
       grind)
    | exact superpose eq84923 eq16
    | exact resolve eq16 eq84923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84968 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq84923
       grind)
    | exact superpose eq84923 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq84923
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq84923
       grind)
    | exact resolve eq12 eq84923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84972 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63 (σ x) (σ y)
       have i₂ := eq84923
       grind)
    | exact superpose eq84923 eq63
    | exact resolve eq63 eq84923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84923
  have eq85064 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq84968
  have eq85118 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq84972
       have i₂ := eq37412 x
       grind)
    | exact superpose eq37412 eq84972
    | exact resolve eq84972 eq37412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84972
  have eq85121 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85064
       have i₂ := eq37412 x
       grind)
    | exact superpose eq37412 eq85064
    | exact resolve eq85064 eq37412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37412 eq85064
  have eq85122 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80025 eq84957
    | exact resolve eq84957 eq80025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80025 eq84957
  have eq85137 : (σ (M.op x x)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85121
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq85121
    | exact resolve eq85121 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85121
  have eq85140 : (σ y) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80123 eq85137
    | exact resolve eq85137 eq80123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80123 eq85137
  have eq85176 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq85118
       grind)
    | exact superpose eq85118 eq10
    | exact resolve eq10 eq85118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85118
  have eq85353 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85176
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq85176
    | exact resolve eq85176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85176
  have eq85401 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63 x y
       have i₂ := eq85353
       grind)
    | exact superpose eq85353 eq63
    | exact resolve eq63 eq85353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq85353
  have eq85493 : x = (M.op x x) := by grind
  clear eq85401
  have eq89618 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq85140
       have i₂ := eq85493
       grind)
    | exact superpose eq85493 eq85140
    | exact resolve eq85140 eq85493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85140
  have eq89619 : x = (M.op x y) := by
    first
    | (have r₁ := eq89618
       have r₂ := eq85122
       grind)
    | exact resolve eq89618 eq85122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85122 eq89618
  have eq89620 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89619
       grind)
    | exact superpose eq89619 eq16
    | exact resolve eq16 eq89619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89625 : x ≠ x ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq89619
       grind)
    | exact superpose eq89619 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq89619
       grind)
    | exact resolve eq12 eq89619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89619
  have eq89723 : (k y x) = (M.op x x) := by grind
  clear eq89625
  have eq89780 : x = (k y x) := by
    first
    | (have i₁ := eq89723
       have i₂ := eq85493
       grind)
    | exact superpose eq85493 eq89723
    | exact resolve eq89723 eq85493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85493 eq89723
  have eq89820 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33993 y x
       have i₂ := eq89780
       grind)
    | exact superpose eq89780 eq33993
    | (have j0 := eq33993 y x
       grind)
    | exact resolve eq33993 eq89780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33993
  have eq89827 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq89820
  have eq89833 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq89827
       have r₂ := eq89620
       grind)
    | exact resolve eq89827 eq89620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89827
  have eq89840 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq89620
       have i₂ := eq89833
       grind)
    | exact superpose eq89833 eq89620
    | exact resolve eq89620 eq89833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89620
  have eq89863 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq74 (σ x) (σ y)
       have i₂ := eq89833
       grind)
    | exact superpose eq89833 eq74
    | exact resolve eq74 eq89833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq89833
  have eq89995 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq89863
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq89863
    | exact resolve eq89863 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89863
  have eq90033 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq89995
       have i₂ := eq89780
       grind)
    | exact superpose eq89780 eq89995
    | exact resolve eq89995 eq89780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89780 eq89995
  have eq90034 : (σ x) = (σ y) := by grind
  clear eq90033
  have eq90052 : False := by grind
  exact eq90052

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq18
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq64 X0 X1
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    grind
  have eq240 : ∀ X1 : G, (M.op X1 X1) = (k (M.op X1 X1) X1) := by
    intro X1
    first
    | (have j0 := eq239 X1
       have j1 := eq70 X1 X1
       grind)
    | (have r₁ := eq239 X1
       have r₂ := eq70 X1 X1
       grind)
    | exact resolve eq239 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq239
  have eq245 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq240 (σ X0)
       grind)
    | exact superpose eq240 eq23
    | exact resolve eq23 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq388 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq388 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq388
    | (have j0 := eq388 (σ X0) (σ X1)
       grind)
    | exact resolve eq388 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq730 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq389 X1 X0
       have i₂ := eq388 X1 X0
       grind)
    | exact superpose eq388 eq389
    | (have j0 := eq389 X1 X0
       have j1 := eq388 (σ X1) (σ X0)
       grind)
    | exact resolve eq389 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq389 (M.op X0 X0) X0
       have i₂ := eq240 X0
       grind)
    | exact superpose eq240 eq389
    | (have j0 := eq389 (M.op X0 X0) X0
       grind)
    | exact resolve eq389 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq389
  have eq12930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq730 x y
       grind)
    | exact superpose eq730 eq16
    | (have j1 := eq730 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq730 x y
       grind)
    | exact resolve eq16 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq12966 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq12930
  have eq12996 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq245 x
       have i₂ := eq12966
       grind)
    | exact superpose eq12966 eq245
    | exact resolve eq245 eq12966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq13016 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq64 (σ x) (σ x)
       have i₂ := eq12966
       grind)
    | exact superpose eq12966 eq64
    | exact resolve eq64 eq12966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12966
  have eq13034 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12996
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq12996
    | exact resolve eq12996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12996
  have eq13051 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq388 y x
       have i₂ := eq13034
       grind)
    | exact superpose eq13034 eq388
    | (have j0 := eq388 y x
       grind)
    | exact resolve eq388 eq13034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq13034
  have eq13052 : y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq13051
  have eq13068 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13016
       grind)
    | exact superpose eq13016 eq16
    | exact resolve eq16 eq13016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13016
  have eq13093 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq13052 eq13068
    | exact resolve eq13068 eq13052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13052 eq13068
  have eq13094 : y = (M.op x x) := by grind
  clear eq13093
  have eq13099 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq731 x
       have i₂ := eq13094
       grind)
    | exact superpose eq13094 eq731
    | exact resolve eq731 eq13094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq13110 : y = (M.op x y) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq13094
       grind)
    | exact superpose eq13094 eq64
    | exact resolve eq64 eq13094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13094
  have eq13123 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13110
       grind)
    | exact superpose eq13110 eq16
    | exact resolve eq16 eq13110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13110
  have eq13281 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq13099
       have r₂ := eq13123
       grind)
    | exact resolve eq13099 eq13123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13099
  have eq13303 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64 (σ x) (σ x)
       have i₂ := eq13281
       grind)
    | exact superpose eq13281 eq64
    | exact resolve eq64 eq13281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq13281
  have eq13312 : False := by grind
  exact eq13312

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pyy_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X2) ≠ X0 ∨ (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = (M.op (M.op (M.op (M.op X0 X1) X2) X2) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X1) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq103 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq105 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
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
  have eq2196 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq103 x y
       grind)
    | exact superpose eq103 eq16
    | (have j1 := eq103 x y
       grind)
    | exact resolve eq16 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2210 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq6948 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq69 X0 X0 X0
       have i₂ := eq73 X0 X0
       grind)
    | exact superpose eq73 eq69
    | (have j1 := eq73 X0 x
       grind)
    | (have r₁ := eq69 X0 X0 X0
       have r₂ := eq73 X0 X0
       grind)
    | exact resolve eq69 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq73
  have eq6955 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6948 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6948
  have eq6956 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6955
  have eq7042 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq6956 (σ X0)
       grind)
    | exact superpose eq6956 eq15
    | exact resolve eq15 eq6956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7065 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7042 X0
       have i₂ := eq6956 X0
       grind)
    | exact superpose eq6956 eq7042
    | exact resolve eq7042 eq6956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6956 eq7042
  have eq11105 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq11251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11105 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq11105
    | (have j0 := eq11105 X0 X1
       grind)
    | exact resolve eq11105 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11105
  have eq64860 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2196
       have i₂ := eq11251 y x
       grind)
    | exact superpose eq11251 eq2196
    | (have j1 := eq11251 (σ x) (σ y)
       grind)
    | (have r₁ := eq2196
       have r₂ := eq11251 y x
       grind)
    | (have r₁ := eq2196
       have r₂ := eq11251 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2196
       have r₂ := eq11251 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2196 eq11251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196
  have eq64861 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq64860
  have eq102285 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq64861
       grind)
    | exact superpose eq64861 eq16
    | exact resolve eq16 eq64861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64861
  have eq102286 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq102285
       have r₂ := eq7065 x
       grind)
    | exact resolve eq102285 eq7065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102285
  have eq102288 : x ≠ x ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq102286
       grind)
    | exact superpose eq102286 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq102286
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq102286
       grind)
    | exact resolve eq12 eq102286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102292 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 x y
       have i₂ := eq102286
       grind)
    | exact superpose eq102286 eq64
    | exact resolve eq64 eq102286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102286
  have eq102309 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq102288
  have eq102320 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq64 (σ x) (σ y)
       have i₂ := eq102292
       grind)
    | exact superpose eq102292 eq64
    | exact resolve eq64 eq102292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq102292
  have eq102341 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102320
       have i₂ := eq7065 x
       grind)
    | exact superpose eq7065 eq102320
    | exact resolve eq102320 eq7065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102320
  have eq102365 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq102341
       grind)
    | exact superpose eq102341 eq10
    | exact resolve eq10 eq102341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102341
  have eq102476 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102365
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq102365
    | exact resolve eq102365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102365
  have eq102505 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq102476
       grind)
    | exact superpose eq102476 eq16
    | exact resolve eq16 eq102476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102476
  have eq102506 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq102505
       have r₂ := eq7065 x
       grind)
    | exact resolve eq102505 eq7065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102505
  have eq102522 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq102506
       grind)
    | exact superpose eq102506 eq10
    | exact resolve eq10 eq102506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102506
  have eq102635 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102522
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq102522
    | exact resolve eq102522 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102522
  have eq102636 : x = (M.op x x) := by grind
  clear eq102635
  have eq180865 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2210 x y
       have i₂ := eq102309
       grind)
    | exact superpose eq102309 eq2210
    | (have j0 := eq2210 x y
       grind)
    | exact resolve eq2210 eq102309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210 eq102309
  have eq180881 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq180865
  have eq180886 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180881
       have i₂ := eq102636
       grind)
    | exact superpose eq102636 eq180881
    | exact resolve eq180881 eq102636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180881
  have eq180887 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq180886
  have eq180891 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq180887
       grind)
    | exact superpose eq180887 eq10
    | exact resolve eq10 eq180887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180887
  have eq181008 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180891
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq180891
    | exact resolve eq180891 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180891
  have eq181053 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181008
       grind)
    | exact superpose eq181008 eq16
    | exact resolve eq16 eq181008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181008
  have eq181054 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq181053
       have r₂ := eq7065 x
       grind)
    | exact resolve eq181053 eq7065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181053
  have eq181062 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181054
       grind)
    | exact superpose eq181054 eq16
    | exact resolve eq16 eq181054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181090 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq181054
       grind)
    | exact superpose eq181054 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq181054
       grind)
    | exact resolve eq12 eq181054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181054
  have eq181136 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
  clear eq181090
  have eq181152 : (k (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq181136
       have i₂ := eq7065 x
       grind)
    | exact superpose eq7065 eq181136
    | exact resolve eq181136 eq7065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7065 eq181136
  have eq181171 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq181152
       have i₂ := eq102636
       grind)
    | exact superpose eq102636 eq181152
    | exact resolve eq181152 eq102636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181152
  have eq181174 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq181171
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq181171
    | exact resolve eq181171 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181171
  have eq181229 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11251 y x
       have i₂ := eq181174
       grind)
    | exact superpose eq181174 eq11251
    | (have j0 := eq11251 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11251 eq181174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11251 eq181174
  have eq181350 : x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq181229
       have r₂ := eq181062
       grind)
    | exact resolve eq181229 eq181062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181229
  have eq181424 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq181062
       have i₂ := eq181350
       grind)
    | exact superpose eq181350 eq181062
    | exact resolve eq181062 eq181350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181350
  have eq181429 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq181424
       have i₂ := eq102636
       grind)
    | exact superpose eq102636 eq181424
    | exact resolve eq181424 eq102636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102636 eq181424
  have eq181430 : x = (M.op x y) := by grind
  clear eq181429
  have eq181437 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq181062
       have i₂ := eq181430
       grind)
    | exact superpose eq181430 eq181062
    | exact resolve eq181062 eq181430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181062 eq181430
  have eq181556 : False := by grind
  exact eq181556

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq22 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq30
  have eq49 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq22 (σ X0) (σ X0)
       grind)
    | exact superpose eq22 eq45
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq79 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq185 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq79 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq79 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq13 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq192 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq193 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq193
    | (have j0 := eq193 X0 X1
       grind)
    | exact resolve eq193 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       have j1 := eq191 X1 X0
       grind)
    | (have r₁ := eq195 X1 X0
       have r₂ := eq191 X0 X1
       grind)
    | (have r₁ := eq195 (k X1 X0) X1
       have r₂ := eq191 X0 X1
       grind)
    | (have r₁ := eq195 X1 X1
       have r₂ := eq191 X1 X1
       grind)
    | exact resolve eq195 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq195
  have eq658 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq199
    | exact resolve eq199 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq199 y x
       grind)
    | exact superpose eq199 eq16
    | (have j1 := eq199 y x
       grind)
    | exact resolve eq16 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq695 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq658 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq658
    | (have j0 := eq658 X0 X1
       grind)
    | exact resolve eq658 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq658
  have eq811 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq695
    | exact resolve eq695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq922 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq811 (τ X1) X0
       grind)
    | exact superpose eq811 eq18
    | (have j1 := eq811 (τ X1) X0
       grind)
    | exact resolve eq18 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1378 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq922 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq922
    | exact resolve eq922 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq1438 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1378 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1378
    | (have j0 := eq1378 X0 X1
       grind)
    | exact resolve eq1378 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1971 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq670
       have i₂ := eq1438 y x
       grind)
    | exact superpose eq1438 eq670
    | (have j1 := eq1438 (σ y) (σ x)
       grind)
    | (have r₁ := eq670
       have r₂ := eq1438 y x
       grind)
    | exact resolve eq670 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq1972 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1971
  have eq1976 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1972
  have eq2186 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq670
       have i₂ := eq1976
       grind)
    | exact superpose eq1976 eq670
    | exact resolve eq670 eq1976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq1976
  have eq2187 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2186
  have eq2188 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq2187
  have eq2195 : (τ (σ y)) = (k (τ (σ y)) x) := by
    first
    | (have i₁ := eq49 x
       have i₂ := eq2188
       grind)
    | exact superpose eq2188 eq49
    | exact resolve eq49 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2213 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22 (σ x) (σ x)
       have i₂ := eq2188
       grind)
    | exact superpose eq2188 eq22
    | exact resolve eq22 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188
  have eq2235 : y = (k y x) := by
    first
    | (have i₁ := eq2195
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2195
    | exact resolve eq2195 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2369 : y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq811 y x
       have i₂ := eq2235
       grind)
    | exact superpose eq2235 eq811
    | (have j0 := eq811 y x
       grind)
    | exact resolve eq811 eq2235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq2235
  have eq2551 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2213
       grind)
    | exact superpose eq2213 eq16
    | exact resolve eq16 eq2213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213
  have eq2738 : (σ y) ≠ (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2551
       have i₂ := eq2369
       grind)
    | exact superpose eq2369 eq2551
    | exact resolve eq2551 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369
  have eq2764 : y = (M.op x x) := by grind
  clear eq2738
  have eq2836 : y = (M.op x y) := by
    first
    | (have i₁ := eq22 x x
       have i₂ := eq2764
       grind)
    | exact superpose eq2764 eq22
    | exact resolve eq22 eq2764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2764
  have eq2859 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2551
       have i₂ := eq2836
       grind)
    | exact superpose eq2836 eq2551
    | exact resolve eq2551 eq2836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551 eq2836
  have eq2885 : False := by grind
  exact eq2885
