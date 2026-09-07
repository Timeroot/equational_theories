import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3545`: `x ◇ y = y ◇ ((x ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_x_pyx_Equation3545 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3545 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3545.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq40 (σ X0)
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq49 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq49
    | exact resolve eq49 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq49
  have eq70 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq194 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq197 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq194 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq194 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq194 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq194 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq194 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq299 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq197 (σ X1) (σ X0)
       grind)
    | exact superpose eq197 eq15
    | (have j1 := eq197 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq301 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq197 (τ X1) X0
       grind)
    | exact superpose eq197 eq18
    | (have j1 := eq197 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq197
  have eq970 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq301
    | exact resolve eq301 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq1007 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq970 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq970
    | (have j0 := eq970 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq970 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq3166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq299 x y
       grind)
    | exact superpose eq299 eq16
    | (have j1 := eq299 x y
       grind)
    | exact resolve eq16 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq3577 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3166
       have i₂ := eq1007 y x
       grind)
    | exact superpose eq1007 eq3166
    | (have j1 := eq1007 (σ x) (σ y)
       grind)
    | (have r₁ := eq3166
       have r₂ := eq1007 y x
       grind)
    | (have r₁ := eq3166
       have r₂ := eq1007 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3166
       have r₂ := eq1007 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3166 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007 eq3166
  have eq3578 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3577
  have eq3744 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3578
       grind)
    | exact superpose eq3578 eq10
    | exact resolve eq10 eq3578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3578
  have eq3791 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3744
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3744
    | exact resolve eq3744 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3744
  have eq3792 : x = y := by grind
  clear eq3791
  have eq3968 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3792
       grind)
    | exact superpose eq3792 eq16
    | exact resolve eq16 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3792
  have eq3969 : False := by grind
  exact eq3969

/-- `Equation3555`: `x ◇ y = y ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3555 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3555 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3555.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
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
  clear eq17
  have eq35 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq104 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq35 x y
       grind)
    | exact superpose eq35 eq16
    | (have j1 := eq35 x y
       grind)
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq317 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq112 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq112
    | (have j0 := eq112 (τ X0) (τ X1)
       grind)
    | exact resolve eq112 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq317 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq317
    | (have j0 := eq317 X0 X1
       grind)
    | exact resolve eq317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq327 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq324
    | (have j0 := eq324 X0 X1
       grind)
    | exact resolve eq324 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq329 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq327
    | (have j0 := eq327 X0 X1
       grind)
    | exact resolve eq327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq330 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq329
    | (have j0 := eq329 X0 X1
       grind)
    | exact resolve eq329 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq331 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq330
    | (have j0 := eq330 X0 X1
       grind)
    | exact resolve eq330 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq332 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq331 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq331
    | (have j0 := eq331 X0 X1
       grind)
    | exact resolve eq331 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq377 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq113 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq113
    | (have j0 := eq113 (τ X0) (τ X1)
       grind)
    | exact resolve eq113 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq384 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq377
    | (have j0 := eq377 X0 X1
       grind)
    | exact resolve eq377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq387 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq384
    | (have j0 := eq384 X0 X1
       grind)
    | exact resolve eq384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq389 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq387
    | (have j0 := eq387 X0 X1
       grind)
    | exact resolve eq387 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq390 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq389
    | (have j0 := eq389 X0 X1
       grind)
    | exact resolve eq389 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq391 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq390 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq390
    | (have j0 := eq390 X0 X1
       grind)
    | exact resolve eq390 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq392 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq391 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq391
    | (have j0 := eq391 X0 X1
       grind)
    | exact resolve eq391 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq437 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq104
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq438 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq437
  have eq3505 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq438
       grind)
    | exact superpose eq438 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq438
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq438
       grind)
    | exact resolve eq13 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3526 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq438
  have eq3528 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq3505
  have eq3536 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3528
       have r₂ := eq3526
       grind)
    | exact resolve eq3528 eq3526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526 eq3528
  have eq3541 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3536
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3536
    | exact resolve eq3536 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3536
  have eq21335 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3541
       grind)
    | exact superpose eq3541 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3541
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3541
       grind)
    | exact resolve eq12 eq3541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3541
  have eq21356 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21335
  have eq21359 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21356
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq21356
    | exact resolve eq21356 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21356
  have eq21618 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq21359
       grind)
    | exact superpose eq21359 eq10
    | exact resolve eq10 eq21359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21359
  have eq21775 : y = (k x y) ∨ (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21618
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq21618
    | exact resolve eq21618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21618
  have eq21782 : (σ x) = (σ (k x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq332 x y
       grind)
    | (have r₁ := eq21775
       have r₂ := eq332 x y
       grind)
    | exact resolve eq21775 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq21775
  have eq21907 : (k x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq21782
       grind)
    | exact superpose eq21782 eq10
    | exact resolve eq10 eq21782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21782
  have eq22065 : x = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21907
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21907
    | exact resolve eq21907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21907
  have eq22066 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq392 x y
       grind)
    | (have r₁ := eq22065
       have r₂ := eq392 x y
       grind)
    | exact resolve eq22065 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq22065
  have eq22299 : y ≠ y ∨ x = y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq22066
       grind)
    | exact superpose eq22066 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22066
       grind)
    | exact resolve eq13 eq22066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22320 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq22322 : x = y ∨ x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq22299
  have eq22330 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22322
       have r₂ := eq22320
       grind)
    | exact resolve eq22322 eq22320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22322
  have eq22809 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq113 x y
       have i₂ := eq22330
       grind)
    | exact superpose eq22330 eq113
    | (have j0 := eq113 x y
       grind)
    | exact resolve eq113 eq22330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq22855 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22809
  have eq137588 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22855
       grind)
    | exact superpose eq22855 eq16
    | exact resolve eq16 eq22855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22855
  have eq138212 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq137588
       have i₂ := eq22066
       grind)
    | exact superpose eq22066 eq137588
    | exact resolve eq137588 eq22066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137588
  have eq138215 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq138212
  have eq138216 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq138215
       have r₂ := eq22320
       grind)
    | exact resolve eq138215 eq22320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138215
  have eq138528 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq138216
       grind)
    | exact superpose eq138216 eq16
    | exact resolve eq16 eq138216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138530 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq138216
       grind)
    | exact superpose eq138216 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq138216
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq138216
       grind)
    | exact resolve eq12 eq138216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138216
  have eq138534 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq138530
  have eq138537 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138534
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq138534
    | exact resolve eq138534 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138534
  have eq138737 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138528
       have i₂ := eq22066
       grind)
    | exact superpose eq22066 eq138528
    | exact resolve eq138528 eq22066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22066 eq138528
  have eq138741 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq138737
       have r₂ := eq22320
       grind)
    | exact resolve eq138737 eq22320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22320 eq138737
  have eq139199 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138537
       have i₂ := eq22330
       grind)
    | exact superpose eq22330 eq138537
    | exact resolve eq138537 eq22330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22330
  have eq139237 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq138537
       grind)
    | exact superpose eq138537 eq10
    | exact resolve eq10 eq138537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138537
  have eq139325 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq139199
  have eq139382 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139237
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq139237
    | exact resolve eq139237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139237
  have eq139409 : x = (M.op x y) := by
    first
    | (have r₁ := eq139325
       have r₂ := eq138741
       grind)
    | exact resolve eq139325 eq138741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138741 eq139325
  have eq139410 : y = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq139382
       have r₂ := eq12 x y
       grind)
    | exact resolve eq139382 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139382
  have eq139850 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112 x y
       have i₂ := eq139410
       grind)
    | exact superpose eq139410 eq112
    | (have j0 := eq112 x y
       grind)
    | exact resolve eq112 eq139410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq139878 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq139850
  have eq146255 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq139878
       grind)
    | exact superpose eq139878 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq139878
       grind)
    | exact resolve eq13 eq139878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146259 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq139878
  have eq146261 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq146255
  have eq146263 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq146261
       have r₂ := eq146259
       grind)
    | exact resolve eq146261 eq146259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146261
  have eq146266 : (σ x) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq146263
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq146263
    | exact resolve eq146263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146263
  have eq146268 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq146266
       have i₂ := eq139410
       grind)
    | exact superpose eq139410 eq146266
    | exact resolve eq146266 eq139410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139410 eq146266
  have eq146269 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq146268
       have r₂ := eq146259
       grind)
    | exact resolve eq146268 eq146259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146259 eq146268
  have eq146546 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq146269
       grind)
    | exact superpose eq146269 eq16
    | exact resolve eq16 eq146269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146269
  have eq146558 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq146546
       have i₂ := eq139409
       grind)
    | exact superpose eq139409 eq146546
    | exact resolve eq146546 eq139409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139409 eq146546
  have eq146559 : False := by grind
  exact eq146559

/-- `Equation3558`: `x ◇ y = y ◇ ((y ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pxy_Equation3558 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3558 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3558.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq57 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq58 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq67 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq57 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq72 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq66 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq66 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq66 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq73 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X1 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq67 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq67 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq103 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq103 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq104 (σ X0)
       grind)
    | exact superpose eq104 eq15
    | exact resolve eq15 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq108
    | exact resolve eq108 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq148 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq14
    | (have j0 := eq14 X1 X1
       grind)
    | exact resolve eq14 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq9
    | exact resolve eq9 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq155 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq148 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq148 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq148 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0
       have i₂ := eq73 X0 X0 X1
       grind)
    | exact superpose eq73 eq104
    | (have j1 := eq73 X0 X0 X1
       grind)
    | exact resolve eq104 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq104
  have eq196 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq181 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq266 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq196 X1 (τ X0)
       grind)
    | exact superpose eq196 eq17
    | (have j1 := eq196 X1 X1
       grind)
    | exact resolve eq17 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq196
  have eq2312 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq266 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq266
    | (have j0 := eq266 X0 X1
       grind)
    | exact resolve eq266 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq2412 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2312 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2312
    | (have j0 := eq2312 X0 X1
       grind)
    | exact resolve eq2312 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2312
  have eq5151 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq155 X0 X1
       grind)
    | exact superpose eq155 eq10
    | (have j1 := eq155 X0 X1
       grind)
    | exact resolve eq10 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq5241 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5151 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5151
    | (have j0 := eq5151 X0 X1
       grind)
    | exact resolve eq5151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5151
  have eq5515 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq5241 X1 (σ X0)
       grind)
    | exact superpose eq5241 eq15
    | (have j1 := eq5241 X1 X1
       grind)
    | exact resolve eq15 eq5241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5241
  have eq6778 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5515 x y
       grind)
    | exact superpose eq5515 eq16
    | (have j1 := eq5515 x y
       grind)
    | exact resolve eq16 eq5515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5515
  have eq6915 : y = (M.op y y) := by
    first
    | (have j1 := eq2412 x y
       grind)
    | (have r₁ := eq6778
       have r₂ := eq2412 x y
       grind)
    | exact resolve eq6778 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412 eq6778
  have eq7177 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq6915
       grind)
    | exact superpose eq6915 eq9
    | exact resolve eq9 eq6915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7178 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq6915
       grind)
    | exact superpose eq6915 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6915
       grind)
    | exact resolve eq12 eq6915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7182 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq151 y X0
       have i₂ := eq6915
       grind)
    | exact superpose eq6915 eq151
    | (have j0 := eq151 y X0
       grind)
    | exact resolve eq151 eq6915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq7183 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq152 y X0
       have i₂ := eq6915
       grind)
    | exact superpose eq6915 eq152
    | exact resolve eq152 eq6915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq6915
  have eq7195 : ∀ X0 : G, (k (σ y) X0) = (M.op (σ y) X0) := by
    intro X0
    first
    | (have j0 := eq7182 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7182
  have eq7197 : ∀ X0 : G, (M.op y X0) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq7178 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7178
  have eq7567 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 y
       have i₂ := eq7197 (τ X0)
       grind)
    | exact superpose eq7197 eq18
    | exact resolve eq18 eq7197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7570 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq7567 X0
       have i₂ := eq7195 X0
       grind)
    | exact superpose eq7195 eq7567
    | exact resolve eq7567 eq7195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7567
  have eq8273 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq29 y X0
       have i₂ := eq7195 X0
       grind)
    | exact superpose eq7195 eq29
    | exact resolve eq29 eq7195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7195
  have eq8316 : ∀ X0 : G, (M.op y (τ X0)) = (τ (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8273 X0
       have i₂ := eq7197 (τ X0)
       grind)
    | exact superpose eq7197 eq8273
    | exact resolve eq8273 eq7197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7197 eq8273
  have eq9603 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (σ (M.op y (M.op y (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq7570 (M.op (σ y) X0)
       have i₂ := eq8316 X0
       grind)
    | exact superpose eq8316 eq7570
    | exact resolve eq7570 eq8316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7570 eq8316
  have eq9604 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq9603 X0
       have i₂ := eq7177 (τ X0)
       grind)
    | exact superpose eq7177 eq9603
    | exact resolve eq9603 eq7177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7177 eq9603
  have eq9656 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq9604 X0
       have i₂ := eq7183 X0
       grind)
    | exact superpose eq7183 eq9604
    | exact resolve eq9604 eq7183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7183 eq9604
  have eq10226 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9656 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9656
    | exact resolve eq9656 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9656
  have eq11513 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10226 x
       grind)
    | exact superpose eq10226 eq16
    | (have r₁ := eq16
       have r₂ := eq10226 x
       grind)
    | exact resolve eq16 eq10226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10226
  have eq11583 : False := by grind
  exact eq11583

/-- `Equation3566`: `x ◇ y = y ◇ ((z ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation3566 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3566 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3566.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X0) X1)) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X1) X3 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X0 X1 X2 X3
       have i₂ := eq9 X1 X3 X0
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq28 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq32
  have eq49 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op x x)
       have i₂ := eq26 x X0 x X1
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq126 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq58 X1 (τ X0)
       grind)
    | exact superpose eq58 eq19
    | (have j1 := eq58 X1 (τ X0)
       grind)
    | exact resolve eq19 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq130 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq289 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq618 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ (k X0 X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) (σ X1)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq80
    | (have j1 := eq59 X1 X0
       grind)
    | exact resolve eq80 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq638 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq3429 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq127 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq127
    | exact resolve eq127 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq3495 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3429 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3429
    | (have j0 := eq3429 X0 X1
       grind)
    | exact resolve eq3429 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3429
  have eq4959 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq126 y x
       grind)
    | exact superpose eq126 eq16
    | (have j1 := eq126 y x
       grind)
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq6346 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq638 (τ X1) (τ X0)
       have i₂ := eq289 X1 X0
       grind)
    | exact superpose eq289 eq638
    | (have j0 := eq638 (τ X1) (τ X0)
       grind)
    | exact resolve eq638 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6386 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6346 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq6346
    | (have j0 := eq6346 X0 X1
       grind)
    | exact resolve eq6346 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6346
  have eq6407 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6386 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq6386
    | (have j0 := eq6386 X0 X1
       grind)
    | exact resolve eq6386 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6386
  have eq6421 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6407 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6407
    | (have j0 := eq6407 X0 X1
       grind)
    | exact resolve eq6407 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6407
  have eq6428 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6421 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6421
    | (have j0 := eq6421 X0 X1
       grind)
    | exact resolve eq6421 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6421
  have eq6434 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6428 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq6428
    | (have j0 := eq6428 X0 X1
       grind)
    | exact resolve eq6428 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6428
  have eq6438 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq6434 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6434
    | (have j0 := eq6434 X0 X1
       grind)
    | exact resolve eq6434 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6434
  have eq6442 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6438 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6438
    | (have j0 := eq6438 X0 X1
       grind)
    | exact resolve eq6438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6438
  have eq54390 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq4959
       have i₂ := eq3495 x y
       grind)
    | exact superpose eq3495 eq4959
    | (have j1 := eq3495 x y
       grind)
    | (have r₁ := eq4959
       have r₂ := eq3495 x y
       grind)
    | (have r₁ := eq4959
       have r₂ := eq3495 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4959
       have r₂ := eq3495 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4959 eq3495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3495 eq4959
  have eq54391 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq54390
  have eq119254 : (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq54391
       grind)
    | exact superpose eq54391 eq10
    | exact resolve eq10 eq54391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54391
  have eq119473 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq119254
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq119254
    | exact resolve eq119254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119254
  have eq119503 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq130 y x
       grind)
    | (have r₁ := eq119473
       have r₂ := eq130 y x
       grind)
    | exact resolve eq119473 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq119473
  have eq121290 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq638 x y
       have i₂ := eq119503
       grind)
    | exact superpose eq119503 eq638
    | (have j0 := eq638 x y
       grind)
    | exact resolve eq638 eq119503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq121297 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq6442 y x
       have i₂ := eq119503
       grind)
    | exact superpose eq119503 eq6442
    | (have j0 := eq6442 y x
       grind)
    | exact resolve eq6442 eq119503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6442
  have eq121302 : y ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq121297
  have eq121309 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq121290
  have eq125825 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ (k X0 X1)))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq618 (τ X1) (τ X0)
       have i₂ := eq289 X0 X1
       grind)
    | exact superpose eq289 eq618
    | (have j0 := eq618 (τ X0) (τ X1)
       grind)
    | exact resolve eq618 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq125851 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq618 y x
       have i₂ := eq119503
       grind)
    | exact superpose eq119503 eq618
    | (have j0 := eq618 y x
       grind)
    | exact resolve eq618 eq119503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq126032 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq125851
  have eq126101 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq126032
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq126032
    | exact resolve eq126032 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126032
  have eq126119 : ∀ X0 X1 : G, (k X0 X1) = (M.op (σ (τ X0)) (k X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq125825 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq125825
    | (have j0 := eq125825 X0 X1
       grind)
    | exact resolve eq125825 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125825
  have eq126303 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq126101
       have r₂ := eq121309
       grind)
    | exact resolve eq126101 eq121309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121309 eq126101
  have eq126320 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126119 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq126119
    | (have j0 := eq126119 X0 X1
       grind)
    | exact resolve eq126119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126119
  have eq126455 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126320 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq126320
    | (have j0 := eq126320 X0 X1
       grind)
    | exact resolve eq126320 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126320
  have eq126530 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126455 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq126455
    | (have j0 := eq126455 X0 X1
       grind)
    | exact resolve eq126455 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126455
  have eq126570 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126530 X0 X1
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq126530
    | (have j0 := eq126530 X0 X1
       grind)
    | exact resolve eq126530 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq126530
  have eq126596 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126570 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq126570
    | (have j0 := eq126570 X0 X1
       grind)
    | exact resolve eq126570 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126570
  have eq126616 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq126596 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq126596
    | (have j0 := eq126596 X0 X1
       grind)
    | exact resolve eq126596 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126596
  have eq126657 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq126303
       grind)
    | exact superpose eq126303 eq16
    | exact resolve eq16 eq126303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126303
  have eq131495 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq126616 y x
       have i₂ := eq119503
       grind)
    | exact superpose eq119503 eq126616
    | (have j0 := eq126616 y x
       grind)
    | exact resolve eq126616 eq119503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119503 eq126616
  have eq131629 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq131495
  have eq131729 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq131629
       have r₂ := eq121302
       grind)
    | exact resolve eq131629 eq121302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121302 eq131629
  have eq132376 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq126657
       have i₂ := eq131729
       grind)
    | exact superpose eq131729 eq126657
    | exact resolve eq126657 eq131729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126657 eq131729
  have eq132544 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq132376
  have eq132545 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq132544
  have eq133074 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq132545
       grind)
    | exact superpose eq132545 eq10
    | exact resolve eq10 eq132545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132545
  have eq133252 : x = y ∨ x = y := by
    first
    | (have i₁ := eq133074
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq133074
    | exact resolve eq133074 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133074
  have eq133253 : x = y := by grind
  clear eq133252
  have eq134785 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq133253
       grind)
    | exact superpose eq133253 eq16
    | exact resolve eq16 eq133253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133253
  have eq134786 : False := by grind
  exact eq134786

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_x_pxx_pxy_Equation3583 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X1) X2 X3
       have i₂ := eq9 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op (M.op X0 X0) X1) X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) X1) (M.op X0 X1)
       have r₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq22 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) X2
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op X0 X1)
       have r₂ := eq22 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq65 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq105 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) ≠ X3 ∨ (M.op X3 (M.op (M.op X1 X1) X2)) = X3 ∨ (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) = (k (M.op (M.op X1 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X1 X1) X2) X3
       have i₂ := eq19 X1 X2 X3 X0
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 (M.op (M.op X1 X1) X2) X3
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq130 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X3) ≠ X3 ∨ (M.op X3 (M.op (M.op X1 X1) X2)) = X3 ∨ (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) = (k (M.op (M.op X1 X1) X2) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq105 x X1 X2 X3
       have i₂ := eq22 (M.op X1 X2) X3 x
       grind)
    | exact superpose eq22 eq105
    | (have j0 := eq105 x X1 X2 X3
       grind)
    | exact resolve eq105 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq161 : ∀ X1 X2 X3 : G, (M.op X1 X2) = X3 ∨ (M.op (M.op X1 X2) X3) ≠ X3 ∨ (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X1 X1) X2)) = (k (M.op (M.op X1 X1) X2) X3) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq130 X1 X2 X3
       have i₂ := eq9 X1 X2 X3
       grind)
    | exact superpose eq9 eq130
    | (have j0 := eq130 X1 X2 X3
       grind)
    | exact resolve eq130 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq173 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X1 X2)) = (k (M.op X1 X2) X3) ∨ (M.op X1 X2) = X3 ∨ (M.op (M.op X1 X2) X3) ≠ X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq161 x X1 X3
       have i₂ := eq26 x X1
       grind)
    | exact superpose eq26 eq161
    | (have j0 := eq161 X1 X2 X3
       grind)
    | exact resolve eq161 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq176 : ∀ X1 X2 X3 : G, (M.op X1 X2) = (k (M.op X1 X2) X3) ∨ (M.op X1 X2) = X3 ∨ (M.op (M.op X1 X2) X3) ≠ X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq173 X1 X2 X3
       have i₂ := eq22 X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq22 eq173
    | (have j0 := eq173 X1 X2 X3
       grind)
    | (have r₁ := eq173 X1 X2 (M.op x X1)
       have r₂ := eq22 x X1 (M.op X1 X2)
       grind)
    | exact resolve eq173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq177 : ∀ X1 X2 X3 : G, (M.op (M.op X1 X2) X3) ≠ X3 ∨ (M.op X1 X2) = (k (M.op X1 X2) X3) := by
    intro X1 X2 X3
    first
    | (have j0 := eq176 X1 X2 X3
       have j1 := eq27 (M.op X1 X2) X3 X3
       grind)
    | (have r₁ := eq176 x X1 X3
       have r₂ := eq27 x X1 (k (M.op x X1) X3)
       grind)
    | (have r₁ := eq176 x X1 X2
       have r₂ := eq27 x X1 X2
       grind)
    | (have r₁ := eq176 X1 X2 (M.op x X1)
       have r₂ := eq27 x X1 (M.op X1 X2)
       grind)
    | exact resolve eq176 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq176
  have eq196 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op (M.op X0 X0) X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq21 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq197 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 X1
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq196
    | exact resolve eq196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq196
  have eq243 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op X2 (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ X1) (σ X0) x
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq22
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq22 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq50 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq247 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq245 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq544 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq247 (M.op X0 X1)
       have i₂ := eq197 X0 X1
       grind)
    | exact superpose eq197 eq247
    | (have j0 := eq247 (M.op X0 X1)
       grind)
    | exact resolve eq247 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq548 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq247 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq247
    | (have j0 := eq247 (τ X0)
       grind)
    | exact resolve eq247 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq549 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq544 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq551 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq548 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq548
    | (have j0 := eq548 X0
       grind)
    | exact resolve eq548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq554 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq551 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq551
    | (have j0 := eq551 X0
       grind)
    | exact resolve eq551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq561 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq554 (τ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq554
    | (have j0 := eq554 (τ X0)
       grind)
    | exact resolve eq554 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq554
  have eq574 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 X3) = (k (M.op X2 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X2 X3 (M.op X0 X1)
       have i₂ := eq22 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq22 eq177
    | (have j0 := eq177 X2 X3 (M.op X0 X1)
       grind)
    | (have r₁ := eq177 X1 X2 (M.op X0 X1)
       have r₂ := eq22 X0 X1 (M.op X1 X2)
       grind)
    | exact resolve eq177 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq576 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (k (M.op X2 X3) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq574 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq832 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq549 X0 X1
       grind)
    | exact superpose eq549 eq22
    | exact resolve eq22 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq1168 : ∀ X0 X1 X2 X3 : G, (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) ∨ (M.op X1 (σ X0)) = (M.op X2 (σ X0)) ∨ (σ X0) = (M.op (σ X3) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (σ X0) X2
       have i₂ := eq243 X0 X3 (M.op X1 X1)
       grind)
    | exact superpose eq243 eq9
    | (have j1 := eq243 X0 X3 (σ X3)
       grind)
    | exact resolve eq9 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3658 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq561 (M.op X0 X1)
       have i₂ := eq576 X0 X1 X0 X1
       grind)
    | exact superpose eq576 eq561
    | (have j0 := eq561 (M.op X0 X1)
       grind)
    | exact resolve eq561 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561 eq576
  have eq3667 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq3658 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3658
  have eq4211 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
       have i₂ := eq3667 X0 X1
       grind)
    | exact superpose eq3667 eq22
    | exact resolve eq22 eq3667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3667
  have eq30179 : ∀ X0 X1 X2 : G, (σ X1) ≠ (M.op X2 (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1168 X1 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq30180 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq30179 X0 X1 x
       have j1 := eq243 X1 X0 (σ X0)
       grind)
    | (have r₁ := eq30179 X0 X0 x
       have r₂ := eq243 X0 X1 x
       grind)
    | (have r₁ := eq30179 X0 X0 (σ X1)
       have r₂ := eq243 X0 X1 x
       grind)
    | exact resolve eq30179 eq243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq30179
  have eq139433 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq30180 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30180
    | exact resolve eq30180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139547 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30180 x y
       grind)
    | exact superpose eq30180 eq16
    | (have j1 := eq30180 x y
       grind)
    | exact resolve eq16 eq30180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30180
  have eq139936 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq139433 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq139433
    | (have j0 := eq139433 X0 X1
       grind)
    | exact resolve eq139433 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq139433
  have eq141147 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq139936 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq139936
    | exact resolve eq139936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139936
  have eq143189 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq141147 (τ X0) X1
       grind)
    | exact superpose eq141147 eq17
    | (have j1 := eq141147 (τ X0) X1
       grind)
    | exact resolve eq17 eq141147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq141147
  have eq146642 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq143189 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq143189
    | exact resolve eq143189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143189
  have eq146717 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq146642 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq146642
    | (have j0 := eq146642 X0 X1
       grind)
    | exact resolve eq146642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146642
  have eq147749 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq139547
       have i₂ := eq146717 x y
       grind)
    | exact superpose eq146717 eq139547
    | (have j1 := eq146717 (σ x) (σ y)
       grind)
    | (have r₁ := eq139547
       have r₂ := eq146717 x y
       grind)
    | exact resolve eq139547 eq146717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139547 eq146717
  have eq147750 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq147749
  have eq148133 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4211 (σ x) (σ y) x
       have i₂ := eq147750
       grind)
    | exact superpose eq147750 eq4211
    | exact resolve eq4211 eq147750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4211 eq147750
  have eq148271 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq148133 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq148133
    | exact resolve eq148133 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148133
  have eq148990 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq148271 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148271
  have eq148991 : y = (M.op x y) := by grind
  clear eq148990
  have eq149273 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq22 x y x
       have i₂ := eq148991
       grind)
    | exact superpose eq148991 eq22
    | exact resolve eq22 eq148991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq149294 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq832 x y x
       have i₂ := eq148991
       grind)
    | exact superpose eq148991 eq832
    | exact resolve eq832 eq148991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq148991
  have eq152106 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq149294 (σ x)
       grind)
    | exact superpose eq149294 eq16
    | exact resolve eq16 eq149294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149294
  have eq152128 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq152106
       have i₂ := eq149273 x
       grind)
    | exact superpose eq149273 eq152106
    | exact resolve eq152106 eq149273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149273 eq152106
  have eq152129 : False := by grind
  exact eq152129

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3587 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X1) X1) X3
       have i₂ := eq9 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq20 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq22 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 x (M.op X0 X1)
       have r₂ := eq22 X0 X1 x
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq29 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k (M.op X0 X1) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X1) X1
       have r₂ := eq27 X0 X1
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq56 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq58 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op X1 X2)
       have i₂ := eq31 X1 X2 (τ X0)
       grind)
    | exact superpose eq31 eq17
    | exact resolve eq17 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq63 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq58
    | exact resolve eq58 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq81 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq102 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq62
    | exact resolve eq62 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39 x y
       grind)
    | exact superpose eq39 eq16
    | (have j1 := eq39 x y
       grind)
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq138 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq81 X0 (M.op X1 X2)
       have i₂ := eq31 X1 X2 (σ X0)
       grind)
    | exact superpose eq31 eq81
    | exact resolve eq81 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq138
    | exact resolve eq138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq525 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq129 (τ X0) (τ X1)
       have i₂ := eq102 X1 X0
       grind)
    | exact superpose eq102 eq129
    | (have j0 := eq129 (τ X0) (τ X1)
       grind)
    | exact resolve eq129 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq540 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq525
    | (have j0 := eq525 X0 X1
       grind)
    | exact resolve eq525 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq546 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq540
    | (have j0 := eq540 X0 X1
       grind)
    | exact resolve eq540 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq551 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq553 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq551
    | (have j0 := eq551 X0 X1
       grind)
    | exact resolve eq551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq554 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq553 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq553
    | (have j0 := eq553 X0 X1
       grind)
    | exact resolve eq553 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq555 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq554
    | (have j0 := eq554 X0 X1
       grind)
    | exact resolve eq554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq594 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq130 (τ X0) (τ X1)
       have i₂ := eq102 X1 X0
       grind)
    | exact superpose eq102 eq130
    | (have j0 := eq130 (τ X0) (τ X1)
       grind)
    | exact resolve eq130 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq601 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq594 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq594
    | (have j0 := eq594 X0 X1
       grind)
    | exact resolve eq594 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq608 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq601 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq601
    | (have j0 := eq601 X0 X1
       grind)
    | exact resolve eq601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq614 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq608 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq608
    | (have j0 := eq608 X0 X1
       grind)
    | exact resolve eq608 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq619 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq614 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq614
    | (have j0 := eq614 X0 X1
       grind)
    | exact resolve eq614 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq620 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq621 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | exact resolve eq620 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq635 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq130 (M.op X1 X0) X0
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq130
    | (have j0 := eq130 (M.op X1 X0) X0
       have j1 := eq56 (σ (M.op X1 X0)) (σ X0)
       grind)
    | exact resolve eq130 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq639 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 (M.op X2 (σ (M.op X0 X1))) X0 X1
       have i₂ := eq56 X2 (σ (M.op X0 X1))
       grind)
    | exact superpose eq56 eq63
    | (have j1 := eq56 X2 (σ (M.op X0 X1))
       grind)
    | exact resolve eq63 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq645 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (σ X0))) X0) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (M.op X1 (σ X0)) X0
       have i₂ := eq56 X1 (σ X0)
       grind)
    | exact superpose eq56 eq62
    | (have j1 := eq56 X1 (σ X0)
       grind)
    | exact resolve eq62 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq647 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) ∨ (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq151 (M.op X2 (τ (M.op X0 X1))) X0 X1
       have i₂ := eq56 X2 (τ (M.op X0 X1))
       grind)
    | exact superpose eq56 eq151
    | (have j1 := eq56 X2 (τ (M.op X0 X1))
       grind)
    | exact resolve eq151 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq647 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq658 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq639 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq661 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq635 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq673 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = X0 ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq645
    | (have j0 := eq645 X0 X1
       grind)
    | exact resolve eq645 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645
  have eq678 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq119
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq679 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq678
  have eq10255 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq31 (σ x) (σ y) X0
       have i₂ := eq679
       grind)
    | exact superpose eq679 eq31
    | exact resolve eq31 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq10260 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq151 X0 (σ x) (σ y)
       have i₂ := eq679
       grind)
    | exact superpose eq679 eq151
    | exact resolve eq151 eq679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq679
  have eq10301 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10260 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq10260
    | exact resolve eq10260 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10260
  have eq128822 : ∀ X0 : G, y = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq673 y (σ x)
       have i₂ := eq10301 X0
       grind)
    | exact superpose eq10301 eq673
    | (have j1 := eq10301 X0
       grind)
    | exact resolve eq673 eq10301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq128860 : ∀ X0 X1 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ (k X1 y) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq654 (σ x) (σ y) x
       have i₂ := eq10301 X0
       grind)
    | exact superpose eq10301 eq654
    | (have j1 := eq10301 X1
       grind)
    | exact resolve eq654 eq10301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10301
  have eq129340 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ (k X1 y) = X1 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq128860 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq128860
    | (have j0 := eq128860 X0 X1
       grind)
    | exact resolve eq128860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128860
  have eq129365 : ∀ X0 : G, y = (k x y) ∨ (σ x) = (σ y) ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq128822 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq128822
    | (have j0 := eq128822 X0
       grind)
    | exact resolve eq128822 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128822
  have eq129401 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq129365 X0
       have j1 := eq621 x y
       grind)
    | (have r₁ := eq129365 X0
       have r₂ := eq621 x y
       grind)
    | (have r₁ := eq129365 y
       have r₂ := eq621 y y
       grind)
    | exact resolve eq129365 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq129365
  have eq129548 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X0 y) ∨ x = (M.op X1 x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 y
       have i₂ := eq129340 X1 (M.op X0 y)
       grind)
    | exact superpose eq129340 eq56
    | (have j0 := eq56 X0 y
       have j1 := eq129340 X1 X1
       grind)
    | exact resolve eq56 eq129340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129340
  have eq129784 : ∀ X0 X1 : G, y = (M.op x y) ∨ y = (M.op X0 y) ∨ x = (M.op X1 x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq129548 x X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129548
  have eq132642 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq129401 (τ X0)
       grind)
    | exact superpose eq129401 eq17
    | exact resolve eq17 eq129401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq129401
  have eq132870 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq132642 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq132642
    | exact resolve eq132642 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132642
  have eq133844 : ∀ X0 : G, y ≠ y ∨ y = (M.op x y) ∨ x = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq129784 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129784
  have eq133846 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq133844 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133844
  have eq134709 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ x = (M.op X1 x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq22 x y x
       have i₂ := eq133846 X0
       grind)
    | exact superpose eq133846 eq22
    | (have j1 := eq133846 X1
       grind)
    | exact resolve eq22 eq133846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133846
  have eq135690 : ∀ X0 X1 X2 : G, x = (M.op X0 x) ∨ y = (M.op X1 y) ∨ x = (M.op X2 x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 x y x
       have i₂ := eq134709 X0 X1
       grind)
    | exact superpose eq134709 eq22
    | (have j1 := eq134709 X1 X0
       grind)
    | exact resolve eq22 eq134709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134709
  have eq136525 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 (σ x) (σ y)
       have i₂ := eq10255 X0
       grind)
    | exact superpose eq10255 eq53
    | (have j1 := eq10255 (σ x)
       grind)
    | (have r₁ := eq53 x y
       have r₂ := eq10255 X0
       grind)
    | exact resolve eq53 eq10255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq10255
  have eq136628 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq136525 (σ x)
       have j1 := eq132870 (σ x)
       grind)
    | (have r₁ := eq136525 X0
       have r₂ := eq132870 X0
       grind)
    | exact resolve eq136525 eq132870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132870 eq136525
  have eq136639 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq136628 X0
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq136628
    | (have j0 := eq136628 X0
       grind)
    | exact resolve eq136628 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136628
  have eq138216 : ∀ X0 X1 : G, x ≠ x ∨ x = (M.op X0 x) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have j0 := eq135690 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135690
  have eq138217 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ y = (M.op X1 y) := by
    intro X0 X1
    first
    | (have j0 := eq138216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138216
  have eq138503 : ∀ X1 X2 : G, (σ y) = (M.op X1 (σ y)) ∨ x = (M.op X2 x) := by
    intro X1 X2
    first
    | (have i₁ := eq658 X1 y X2
       have i₂ := eq138217 x X1
       grind)
    | exact superpose eq138217 eq658
    | (have j1 := eq138217 X2 X1
       grind)
    | exact resolve eq658 eq138217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152135 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq138503 (σ x) X0
       grind)
    | exact superpose eq138503 eq16
    | (have j1 := eq138503 x X0
       grind)
    | exact resolve eq16 eq138503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138503
  have eq161014 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ x = (M.op X0 x) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq152135 X0
       have i₂ := eq138217 X1 x
       grind)
    | exact superpose eq138217 eq152135
    | (have j0 := eq152135 X0
       have j1 := eq138217 X0 X1
       grind)
    | exact resolve eq152135 eq138217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138217 eq152135
  have eq161021 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ x = (M.op X1 x) := by
    intro X0 X1
    first
    | (have j0 := eq161014 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161014
  have eq161182 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq161021 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161021
  have eq161183 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq161182 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161182
  have eq161247 : ∀ X1 : G, (σ x) = (M.op X1 (σ x)) := by
    intro X1
    first
    | (have i₁ := eq658 x x x
       have i₂ := eq161183 x
       grind)
    | exact superpose eq161183 eq658
    | exact resolve eq658 eq161183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799986 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ y))) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq81 X0 (σ y)
       have i₂ := eq136639 (σ X0)
       grind)
    | exact superpose eq136639 eq81
    | exact resolve eq81 eq136639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq136639
  have eq799989 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq799986 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq799986
    | exact resolve eq799986 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799986
  have eq799990 : ∀ X0 : G, (σ x) = (σ (k x y)) ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq799989 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq799989
    | exact resolve eq799989 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799989
  have eq799991 : ∀ X0 : G, (k x y) = (τ (σ x)) ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq799990 X0
       grind)
    | exact superpose eq799990 eq10
    | (have j1 := eq799990 X0
       grind)
    | exact resolve eq10 eq799990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799990
  have eq799996 : ∀ X0 : G, x = (k x y) ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq799991 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq799991
    | (have j0 := eq799991 x
       grind)
    | exact resolve eq799991 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799991
  have eq799997 : ∀ X0 : G, (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq799996 X0
       have j1 := eq555 x y
       grind)
    | (have r₁ := eq799996 X0
       have r₂ := eq555 x y
       grind)
    | (have r₁ := eq799996 X0
       have r₂ := eq555 X0 y
       grind)
    | exact resolve eq799996 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq799996
  have eq800019 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq56 X0 y
       have i₂ := eq799997 (M.op X0 y)
       grind)
    | exact superpose eq799997 eq56
    | (have j0 := eq56 X0 y
       grind)
    | exact resolve eq56 eq799997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq799997
  have eq800150 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq800019 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800019
  have eq800521 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq800150 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800150
  have eq800523 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq800521
  have eq800763 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq22 x y x
       have i₂ := eq800523
       grind)
    | exact superpose eq800523 eq22
    | exact resolve eq22 eq800523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq800792 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq658 x y x
       have i₂ := eq800523
       grind)
    | exact superpose eq800523 eq658
    | exact resolve eq658 eq800523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq800817 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq800523
  have eq805952 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq800792 (σ x)
       grind)
    | exact superpose eq800792 eq16
    | exact resolve eq16 eq800792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800792
  have eq809215 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq805952
       have i₂ := eq800763 x
       grind)
    | exact superpose eq800763 eq805952
    | exact resolve eq805952 eq800763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800763 eq805952
  have eq809218 : x = y ∨ x = (M.op x y) := by grind
  clear eq809215
  have eq809238 : x = (M.op x y) := by
    first
    | (have r₁ := eq809218
       have r₂ := eq800817
       grind)
    | exact resolve eq809218 eq800817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800817 eq809218
  have eq809496 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq661 y x
       have i₂ := eq809238
       grind)
    | exact superpose eq809238 eq661
    | (have j0 := eq661 (σ y) (σ x)
       grind)
    | exact resolve eq661 eq809238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq885663 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq654 (σ x) (σ y) x
       have i₂ := eq809496
       grind)
    | exact superpose eq809496 eq654
    | exact resolve eq654 eq809496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq809496
  have eq885675 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq885663 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq885663
    | exact resolve eq885663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885663
  have eq885740 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq885675 X0
       grind)
    | exact superpose eq885675 eq16
    | (have j1 := eq885675 X0
       grind)
    | exact resolve eq16 eq885675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885675
  have eq885901 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq885740 X0
       have i₂ := eq809238
       grind)
    | exact superpose eq809238 eq885740
    | (have j0 := eq885740 X0
       grind)
    | exact resolve eq885740 eq809238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885740
  have eq885902 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq885901 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885901
  have eq886222 : x = y ∨ x = y := by
    first
    | (have i₁ := eq809238
       have i₂ := eq885902 x
       grind)
    | exact superpose eq885902 eq809238
    | exact resolve eq809238 eq885902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809238 eq885902
  have eq886223 : x = y := by grind
  clear eq886222
  have eq886299 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq886223
       grind)
    | exact superpose eq886223 eq16
    | exact resolve eq16 eq886223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886223
  have eq888104 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq886299
       have i₂ := eq161183 x
       grind)
    | exact superpose eq161183 eq886299
    | exact resolve eq886299 eq161183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161183 eq886299
  have eq888105 : False := by grind
  exact eq888105

/-- `Equation3591`: `x ◇ y = z ◇ ((x ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pyx_Equation3591 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3591 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3591.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X2) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X2) X1) (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op (M.op X0 X2) X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 (M.op X2 X3)) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 (M.op X2 X3)) X1) X3
       have i₂ := eq9 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq59 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq60 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq59 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq72 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq67 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq73 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq68 X0 X1 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq68 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq104 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq105 (σ X0)
       grind)
    | exact superpose eq105 eq15
    | exact resolve eq15 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq105 (τ X0)
       grind)
    | exact superpose eq105 eq33
    | exact resolve eq33 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq111
    | exact resolve eq111 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq120 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq109 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq109
    | exact resolve eq109 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq132 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X1)) ∨ (M.op X3 X3) = X3 ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X2 X0 X1
       have i₂ := eq14 X3 X0
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X3 X3
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 (M.op X3 X4)) X1)) = (M.op (M.op (M.op X3 X2) X4) (M.op X0 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X3 X4 X2 (M.op (M.op X0 (M.op X3 X4)) X1)
       have i₂ := eq9 X0 X1 (M.op X3 X4)
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X2 X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X0) (M.op (M.op X2 X3) X1) X3
       have i₂ := eq23 X2 X3 X0 X1
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X3) X4) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X3) X4 (M.op (M.op X2 X3) X1)
       have i₂ := eq23 X2 X3 X0 X1
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op (M.op X0 X2) X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq132 X0 X1 X2 X3
       have j1 := eq12 X3 X0
       grind)
    | (have r₁ := eq132 X0 X1 X2 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq132 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X2 X1)) ∨ (k X3 X0) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq171 X0 X1 X2 X3
       have i₂ := eq149 X2 X1 X0 X2
       grind)
    | exact superpose eq149 eq171
    | (have j0 := eq171 X0 X1 X2 X3
       grind)
    | exact resolve eq171 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq171
  have eq185 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq9
    | exact resolve eq9 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) (M.op X4 X5)) = (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq24 X4 X5 X3 (M.op (M.op X1 (M.op X3 X0)) X2)
       have i₂ := eq24 X1 X2 X3 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op (M.op X2 X0) X3) X4)) = (M.op (M.op X2 X3) (M.op (M.op X0 X1) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op (M.op X2 X0) X3) X4 (M.op X2 X3) X1
       have i₂ := eq23 X2 X3 X0 X1
       grind)
    | exact superpose eq23 eq24
    | exact resolve eq24 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 X5) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq23 X3 X5 (M.op (M.op X1 (M.op X3 X0)) X2) X4
       have i₂ := eq24 X1 X2 X3 X0
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op (M.op (M.op X4 X3) X5) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq23 X4 X5 X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)
       have i₂ := eq24 X1 X2 (M.op X4 X5) X0
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op (M.op X1 (M.op (M.op X3 X4) X0)) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 (M.op (M.op X3 X4) X0)) X2) X4
       have i₂ := eq24 X1 X2 (M.op X3 X4) X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X1 (M.op (M.op X4 X5) X0)) X2)) = (M.op X3 (M.op (M.op X0 (M.op X4 X5)) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq217 X0 X1 X2 X3 X4 X5
       have i₂ := eq144 X0 (M.op X1 X2) X3 X4 X5
       grind)
    | exact superpose eq144 eq217
    | exact resolve eq217 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq223 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X3 X0)) X2) X4) = (M.op (M.op (M.op X0 X3) (M.op X1 X2)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq215 X0 X1 X2 X3 X4 x
       have i₂ := eq150 X3 x X0 (M.op X1 X2) X4
       grind)
    | exact superpose eq150 eq215
    | exact resolve eq215 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq232 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X4 (M.op X0 (M.op X1 X2))) X5)) = (M.op (M.op X3 X0) (M.op (M.op X4 (M.op X1 X2)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq199 X0 X1 X2 X3 X4 X5
       have i₂ := eq144 X4 X5 (M.op X3 X0) X1 X2
       grind)
    | exact superpose eq144 eq199
    | exact resolve eq199 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq308 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ (M.op X0 X0)) X1) X2) = (M.op (M.op (M.op (σ X0) X1) X3) (M.op (M.op (σ X0) X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (σ X0) X3 (M.op (σ (M.op X0 X0)) X1) X2
       have i₂ := eq185 X0 X1
       grind)
    | exact superpose eq185 eq23
    | exact resolve eq23 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq310 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (σ (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq308 X0 X1 X2 x
       have i₂ := eq23 (σ X0) x X1 X2
       grind)
    | exact superpose eq23 eq308
    | exact resolve eq308 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq365 : ∀ X0 X1 X2 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq73 X0 X2 (τ X1)
       grind)
    | exact superpose eq73 eq17
    | (have j1 := eq73 X0 X2 X2
       grind)
    | exact resolve eq17 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq73
  have eq495 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (σ (τ (M.op X0 X0))) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq310 (τ X0) X1 X2
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq310
    | exact resolve eq310 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq498 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op (M.op X0 (σ (M.op X2 X2))) X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq310 X2 (M.op (M.op X0 (σ (M.op X2 X2))) X1) X3
       have i₂ := eq9 X0 X1 (σ (M.op X2 X2))
       grind)
    | exact superpose eq9 eq310
    | exact resolve eq310 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (σ (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ (M.op X2 X2)) X1 X0
       have i₂ := eq310 X2 X0 X1
       grind)
    | exact superpose eq310 eq9
    | exact resolve eq9 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X1) X4) (M.op (M.op (M.op (σ (M.op X3 X3)) X0) X4) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 (M.op (σ (M.op X3 X3)) X0) X4 X1 X2
       have i₂ := eq310 X3 X0 X1
       grind)
    | exact superpose eq310 eq23
    | exact resolve eq23 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 (M.op (σ (M.op X3 X3)) X0)) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq515 X0 X1 X2 X3 x
       have i₂ := eq150 (M.op (σ (M.op X3 X3)) X0) x X0 X1 X2
       grind)
    | exact superpose eq150 eq515
    | exact resolve eq515 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq515
  have eq549 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq495 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq495
    | exact resolve eq495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq553 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 (σ (M.op X3 X3))) (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq536 X0 X1 X2 X3
       have i₂ := eq223 X0 X0 X1 (σ (M.op X3 X3)) X2
       grind)
    | (have i₁ := eq536 X0 (M.op X1 X2) x X3
       have i₂ := eq223 X0 X1 X2 (M.op (σ (M.op X3 X3)) X0) x
       grind)
    | exact superpose eq223 eq536
    | exact resolve eq536 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223 eq536
  have eq558 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq553 X0 X1 X2 x
       have i₂ := eq498 X0 (M.op X0 X1) x X2
       grind)
    | exact superpose eq498 eq553
    | exact resolve eq553 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq553
  have eq659 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op (M.op (M.op (M.op X3 X3) X2) X0) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (M.op X3 X3) X0 X2 X1
       have i₂ := eq549 X3 X0 X1
       grind)
    | exact superpose eq549 eq23
    | exact resolve eq23 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op (M.op X0 X1) (M.op (M.op (M.op X3 X3) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (M.op X3 X3) X1 X0 X2
       have i₂ := eq549 X3 X0 X1
       grind)
    | exact superpose eq549 eq23
    | exact resolve eq23 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X2) X1 X0
       have i₂ := eq549 X2 X0 X1
       grind)
    | exact superpose eq549 eq9
    | exact resolve eq9 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq697 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op (M.op X0 (M.op X3 X3)) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq660 X0 X1 X2 X3
       have i₂ := eq208 (M.op X3 X3) X1 X0 X1 X2
       grind)
    | exact superpose eq208 eq660
    | exact resolve eq660 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq660
  have eq698 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 (M.op (M.op X3 X3) X0)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq659 X0 X1 X2 X3
       have i₂ := eq144 X0 X1 X2 (M.op X3 X3) X0
       grind)
    | exact superpose eq144 eq659
    | exact resolve eq659 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq719 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op (M.op X0 (M.op X3 X3)) X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq697 X0 x X2 X3
       have i₂ := eq9 (M.op X0 (M.op X3 X3)) X2 x
       grind)
    | exact superpose eq9 eq697
    | exact resolve eq697 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq720 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op (M.op X0 (M.op X3 X3)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq698 X0 X1 X2 X3
       have i₂ := eq221 X0 X0 X1 X2 X3 X3
       grind)
    | (have i₁ := eq698 x (M.op X1 X2) X3 X3
       have i₂ := eq221 x X1 X2 X3 (M.op X3 X3) x
       grind)
    | exact superpose eq221 eq698
    | exact resolve eq698 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq728 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq720 X0 X1 X2 x
       have i₂ := eq719 X0 (M.op X0 X1) x
       grind)
    | exact superpose eq719 eq720
    | exact resolve eq720 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq853 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X1) X3) = (M.op (M.op X2 (M.op X0 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq558 X2 (M.op (M.op X0 X2) X1) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq558
    | exact resolve eq558 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq897 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X2 X1 X2 X0
       have i₂ := eq558 X2 X0 X1
       grind)
    | exact superpose eq558 eq24
    | exact resolve eq24 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X1 (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq558 (M.op X1 X2) X0 (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X3)
       grind)
    | exact superpose eq558 eq23
    | exact resolve eq23 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X3 X4)) = (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X3 (M.op X0 X1)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X3 X4 (M.op X2 (M.op X2 X0)) X1
       have i₂ := eq558 X2 X0 X1
       grind)
    | exact superpose eq558 eq24
    | exact resolve eq24 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq938 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X3 X4)) = (M.op X2 (M.op (M.op X3 (M.op (M.op X2 X0) (M.op X0 X1))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq902 X0 X1 X2 X3 X4
       have i₂ := eq232 (M.op X2 X0) X0 X1 X2 X3 X4
       grind)
    | exact superpose eq232 eq902
    | exact resolve eq902 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq942 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq898 X0 X1 X2 X3
       have i₂ := eq221 X0 X1 X3 X0 X1 X2
       grind)
    | (have i₁ := eq898 x X0 X2 (M.op X1 X2)
       have i₂ := eq221 X0 X1 X2 x (M.op X0 X2) x
       grind)
    | exact superpose eq221 eq898
    | exact resolve eq898 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq973 : ∀ X0 X1 X3 X4 : G, (M.op X1 (M.op X3 X4)) = (M.op X0 (M.op (M.op X0 X1) (M.op X3 X4))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq938 X0 X1 x X3 X4
       have i₂ := eq219 (M.op X0 X1) X3 X4 x X0
       grind)
    | exact superpose eq219 eq938
    | exact resolve eq938 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq938
  have eq976 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X1 (M.op (M.op X0 (M.op X1 X2)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq942 X0 X1 X2 X3
       have i₂ := eq897 X1 X3 (M.op X0 (M.op X1 X2))
       grind)
    | (have i₁ := eq942 X0 X1 X2 X3
       have i₂ := eq897 (M.op X0 (M.op X1 X2)) X3 X1
       grind)
    | exact superpose eq897 eq942
    | exact resolve eq942 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq993 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X2 (M.op X0 X3))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq976 X0 x X2 X3
       have i₂ := eq24 X0 X3 x X2
       grind)
    | exact superpose eq24 eq976
    | exact resolve eq976 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1229 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op X1 X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq661 (σ X0) (σ X0) X1
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq661
    | exact resolve eq661 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1254 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X0 X0)) X2) = (M.op X1 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq661 X1 X2 (τ X0)
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq661
    | exact resolve eq661 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1258 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq661 X0 X1 x
       have i₂ := eq661 X2 X1 x
       grind)
    | exact superpose eq661 eq661
    | exact resolve eq661 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1290 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X4 (M.op (M.op X4 X2) X1)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 X4 (M.op (M.op X4 X2) X1) X2 X3
       have i₂ := eq661 (M.op X4 X2) X1 X0
       grind)
    | exact superpose eq661 eq23
    | exact resolve eq23 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1292 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op (M.op (σ (M.op X3 X3)) X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq310 X3 X2 (M.op (M.op (σ (M.op X3 X3)) X2) X1)
       have i₂ := eq661 (M.op (σ (M.op X3 X3)) X2) X1 X0
       grind)
    | exact superpose eq661 eq310
    | exact resolve eq310 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1307 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op (M.op (M.op X4 X4) X2) X1) (M.op (M.op X0 (M.op X0 X1)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq23 (M.op X4 X4) X1 X2 X3
       have i₂ := eq661 X0 X1 X4
       grind)
    | exact superpose eq661 eq23
    | exact resolve eq23 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1320 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X3 (M.op X2 X2)
       have i₂ := eq661 X0 (M.op (M.op X1 (M.op X2 X2)) X3) X2
       grind)
    | exact superpose eq661 eq9
    | exact resolve eq9 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq1339 : ∀ X0 X1 X3 : G, (M.op X1 X3) = (M.op X0 (M.op X0 (M.op X1 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1320 X0 X1 x X3
       have i₂ := eq719 X1 X3 x
       grind)
    | exact superpose eq719 eq1320
    | exact resolve eq1320 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq1320
  have eq1348 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X4 X4) X1)) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1307 X0 X1 X2 X3 X4
       have i₂ := eq144 (M.op X0 (M.op X0 X1)) X3 X2 (M.op X4 X4) X1
       grind)
    | exact superpose eq144 eq1307
    | exact resolve eq1307 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq1358 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (σ (M.op X3 X3)) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1292 X0 X1 x X3
       have i₂ := eq9 (σ (M.op X3 X3)) X1 x
       grind)
    | exact superpose eq9 eq1292
    | exact resolve eq1292 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq1359 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X1 (M.op X4 X2)) (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1290 X0 X1 X2 X3 X4
       have i₂ := eq221 X1 X4 X3 (M.op (M.op X0 X0) X1) X4 X2
       grind)
    | (have i₁ := eq1290 X0 x X2 (M.op X1 X2) X0
       have i₂ := eq221 X0 X1 X2 (M.op (M.op X0 X0) x) (M.op X0 X2) x
       grind)
    | exact superpose eq221 eq1290
    | exact resolve eq1290 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq1397 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op X1 (M.op X4 X4)) (M.op (M.op X0 (M.op X0 X1)) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1348 X0 X1 X2 X3 X4
       have i₂ := eq221 X1 (M.op X0 (M.op X0 X1)) X3 X2 X4 X4
       grind)
    | (have i₁ := eq1348 X0 x X3 (M.op X1 X2) X4
       have i₂ := eq221 (M.op X0 (M.op X0 x)) X1 X2 X3 (M.op X4 X4) x
       grind)
    | exact superpose eq221 eq1348
    | exact resolve eq1348 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1348
  have eq1400 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op (M.op X1 (M.op X4 X2)) (M.op X0 X1)) (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1359 X0 X1 X2 X3 X4
       have i₂ := eq144 (M.op X1 (M.op X4 X2)) (M.op X4 X3) X0 X0 X1
       grind)
    | exact superpose eq144 eq1359
    | exact resolve eq1359 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq1359
  have eq1424 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op X1 (M.op (M.op X0 (M.op (M.op X4 X4) (M.op X0 X1))) X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1397 X0 X1 X2 X3 X4
       have i₂ := eq232 (M.op X4 X4) X0 X1 X1 X0 X3
       grind)
    | exact superpose eq232 eq1397
    | exact resolve eq1397 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq1397
  have eq1426 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X1 (M.op (M.op X1 (M.op X4 X2)) (M.op X4 X3))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1400 x X1 X2 X3 X4
       have i₂ := eq24 (M.op X1 (M.op X4 X2)) (M.op X4 X3) x X1
       grind)
    | exact superpose eq24 eq1400
    | exact resolve eq1400 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq1433 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X4 X4)) (M.op X0 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1424 X0 X1 X2 X3 X4
       have i₂ := eq221 (M.op X0 X1) X0 X3 X1 X4 X4
       grind)
    | (have i₁ := eq1424 X0 X3 X2 (M.op X1 X2) X4
       have i₂ := eq221 X0 X1 X2 X3 (M.op X4 X4) (M.op X0 X3)
       grind)
    | exact superpose eq221 eq1424
    | exact resolve eq1424 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq1424
  have eq1434 : ∀ X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op X4 X2) (M.op X4 X3)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq1426 x X2 X3 X4
       have i₂ := eq973 x (M.op X4 X2) X4 X3
       grind)
    | (have i₁ := eq1426 x X2 X3 X4
       have i₂ := eq973 x x (M.op x (M.op X4 X2)) (M.op X4 X3)
       grind)
    | exact superpose eq973 eq1426
    | exact resolve eq1426 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973 eq1426
  have eq1436 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op X1 (M.op X0 (M.op (M.op (M.op X0 X1) (M.op X4 X4)) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1433 X0 X1 X2 X3 X4
       have i₂ := eq897 X0 X3 (M.op (M.op X0 X1) (M.op X4 X4))
       grind)
    | (have i₁ := eq1433 X0 X1 X2 X3 X4
       have i₂ := eq897 (M.op (M.op X0 X1) (M.op X4 X4)) X3 X0
       grind)
    | exact superpose eq897 eq1433
    | exact resolve eq1433 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1433
  have eq1437 : ∀ X2 X3 X4 : G, (M.op X2 X3) = (M.op X4 (M.op (M.op X4 X2) X3)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq1434 X2 X3 X4
       have i₂ := eq897 X4 X3 (M.op X4 X2)
       grind)
    | (have i₁ := eq1434 X2 X3 X4
       have i₂ := eq897 (M.op X4 X2) X3 X4
       grind)
    | exact superpose eq897 eq1434
    | exact resolve eq1434 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq1434
  have eq1439 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op X1 (M.op X0 (M.op (M.op X1 (M.op X0 (M.op X4 X4))) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1436 X0 X1 X2 X3 X4
       have i₂ := eq853 X0 (M.op X4 X4) X1 X3
       grind)
    | (have i₁ := eq1436 X0 X1 X2 X3 X1
       have i₂ := eq853 X1 X1 (M.op X0 X1) X3
       grind)
    | exact superpose eq853 eq1436
    | exact resolve eq1436 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436
  have eq1441 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op X1 (M.op (M.op X4 X4) (M.op X1 X3)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1439 x X1 X2 X3 X4
       have i₂ := eq24 X1 X3 x (M.op X4 X4)
       grind)
    | exact superpose eq24 eq1439
    | exact resolve eq1439 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1443 : ∀ X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op X4 X4) X3)) := by
    intro X2 X3 X4
    first
    | (have i₁ := eq1441 x X2 X3 X4
       have i₂ := eq993 x (M.op X4 X4) X3
       grind)
    | (have i₁ := eq1441 X2 X2 X3 X4
       have i₂ := eq993 x X2 (M.op (M.op X4 X4) (M.op X2 X3))
       grind)
    | exact superpose eq993 eq1441
    | exact resolve eq1441 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441
  have eq1989 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X1 (M.op X4 X0)) X2)) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq728 X4 (M.op (M.op X1 (M.op X4 X0)) X2) X3
       have i₂ := eq24 X1 X2 X4 X0
       grind)
    | exact superpose eq24 eq728
    | exact resolve eq728 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3425 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op (M.op (σ (M.op X3 X3)) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq993 X1 (M.op (σ (M.op X3 X3)) X0) X2
       have i₂ := eq310 X3 X0 (M.op X1 X2)
       grind)
    | exact superpose eq310 eq993
    | exact resolve eq993 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq3453 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op X1 X2) X1
       have i₂ := eq993 X1 (M.op X0 X1) X2
       grind)
    | exact superpose eq993 eq9
    | exact resolve eq9 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3529 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 X2))) = (M.op (σ (M.op X3 X3)) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3425 X0 X1 X2 X3
       have i₂ := eq3453 (σ (M.op X3 X3)) X0 X2
       grind)
    | exact superpose eq3453 eq3425
    | exact resolve eq3425 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3425
  have eq3583 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op (σ (M.op X3 X3)) (M.op X0 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq3529 X0 x X2 X3
       have i₂ := eq993 x X0 X2
       grind)
    | (have i₁ := eq3529 X0 X2 X2 X3
       have i₂ := eq993 X0 X2 (M.op X0 (M.op X2 X2))
       grind)
    | exact superpose eq993 eq3529
    | exact resolve eq3529 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3529
  have eq5103 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (M.op X1 (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1258 X1 (τ X0) (τ X0)
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq1258
    | exact resolve eq1258 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6063 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1339 X0 (σ X0) (σ X0)
       have i₂ := eq120 X0
       grind)
    | exact superpose eq120 eq1339
    | exact resolve eq1339 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq6066 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1339 X0 (τ X0) (τ X0)
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq1339
    | exact resolve eq1339 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq7110 : ∀ X0 X1 X2 X3 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) X2) = (M.op X3 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq177 (σ X0) X2 X3 (σ X1)
       grind)
    | exact superpose eq177 eq15
    | (have j1 := eq177 (σ X0) X2 X3 X3
       grind)
    | exact resolve eq15 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq10665 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) ≠ (M.op X0 (M.op X0 (σ (M.op X1 X1)))) ∨ (k (σ (M.op X1 X1)) X2) = (M.op X2 (σ (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ (M.op X1 X1)) X2
       have i₂ := eq510 X0 (σ (M.op X1 X1)) X1
       grind)
    | exact superpose eq510 eq12
    | (have j0 := eq12 (σ (M.op X1 X1)) X2
       grind)
    | exact resolve eq12 eq510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10801 : ∀ X1 X2 : G, (k (σ (M.op X1 X1)) X2) = (M.op X2 (σ (M.op X1 X1))) := by
    intro X1 X2
    first
    | (have j0 := eq10665 x X1 X2
       grind)
    | (have r₁ := eq10665 X1 x X2
       have r₂ := eq6063 x X1
       grind)
    | exact resolve eq10665 eq6063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6063 eq10665
  have eq14007 : ∀ X0 X1 X2 : G, (τ (M.op X1 X1)) ≠ (M.op X0 (M.op X0 (τ (M.op X1 X1)))) ∨ (k (τ (M.op X1 X1)) X2) = (M.op X2 (τ (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (τ (M.op X1 X1)) X2
       have i₂ := eq1254 X1 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1254 eq12
    | (have j0 := eq12 (τ (M.op X1 X1)) X2
       grind)
    | exact resolve eq12 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq14313 : ∀ X1 X2 : G, (k (τ (M.op X1 X1)) X2) = (M.op X2 (τ (M.op X1 X1))) := by
    intro X1 X2
    first
    | (have j0 := eq14007 x X1 X2
       grind)
    | (have r₁ := eq14007 X1 x X2
       have r₂ := eq6066 x X1
       grind)
    | exact resolve eq14007 eq6066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6066 eq14007
  have eq15056 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op (σ (M.op X0 X0)) (M.op X1 X1)) ∨ (M.op X2 (M.op X1 X1)) = (k (M.op X1 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X1) X2
       have i₂ := eq1358 X1 (M.op X1 X1) X0
       grind)
    | exact superpose eq1358 eq12
    | (have j0 := eq12 (M.op X1 X1) X2
       grind)
    | exact resolve eq12 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq15405 : ∀ X1 X2 : G, (M.op X2 (M.op X1 X1)) = (k (M.op X1 X1) X2) := by
    intro X1 X2
    first
    | (have j0 := eq15056 x X1 X2
       grind)
    | (have r₁ := eq15056 x X2 X2
       have r₂ := eq3583 X2 X2 x
       grind)
    | exact resolve eq15056 eq3583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3583 eq15056
  have eq16030 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = (τ (M.op (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 X1) X0
       have i₂ := eq15405 X1 (σ X0)
       grind)
    | exact superpose eq15405 eq22
    | exact resolve eq22 eq15405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq16034 : ∀ X0 X1 : G, (M.op X0 (τ (M.op X1 X1))) = (τ (M.op (σ X0) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16030 X0 X1
       have i₂ := eq14313 X1 X0
       grind)
    | exact superpose eq14313 eq16030
    | exact resolve eq16030 eq14313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16030
  have eq56995 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X2 X2) = X2 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq365 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq365
    | (have j0 := eq365 X1 X1 X2
       grind)
    | exact resolve eq365 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq57557 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X2 X2) = X2 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56995 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56995
    | (have j0 := eq56995 X0 X1 X2
       grind)
    | exact resolve eq56995 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56995
  have eq73529 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X1 X1))) = (σ (k (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X1 X1) X0
       have i₂ := eq10801 X1 (σ X0)
       grind)
    | exact superpose eq10801 eq15
    | exact resolve eq15 eq10801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10801
  have eq73576 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X1 X1))) = (M.op (σ X0) (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq73529 X0 X1
       have i₂ := eq15405 X1 X0
       grind)
    | exact superpose eq15405 eq73529
    | exact resolve eq73529 eq15405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73529
  have eq118778 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X1 X1))) = (τ (k (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 (M.op X1 X1)
       have i₂ := eq14313 X1 (τ X0)
       grind)
    | exact superpose eq14313 eq33
    | exact resolve eq33 eq14313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq14313
  have eq118817 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 X1))) = (M.op (τ X0) (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq118778 X0 X1
       have i₂ := eq15405 X1 X0
       grind)
    | exact superpose eq15405 eq118778
    | exact resolve eq118778 eq15405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15405 eq118778
  have eq170442 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (σ X2)) = (M.op (σ X2) (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1229 X2 (M.op X0 (M.op X0 X1))
       have i₂ := eq728 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq728 eq1229
    | exact resolve eq1229 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq171164 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (σ X2)) = (σ (M.op X2 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq170442 X0 X1 X2
       have i₂ := eq73576 X2 X2
       grind)
    | exact superpose eq73576 eq170442
    | exact resolve eq170442 eq73576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73576 eq170442
  have eq171520 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (σ X2)) = (σ (M.op X2 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171164 X0 X1 X2
       have i₂ := eq853 X0 X1 (M.op X0 X1) (σ X2)
       grind)
    | (have i₁ := eq171164 X0 (M.op X0 X1) X2
       have i₂ := eq853 X0 X1 (M.op X0 (M.op X0 (M.op X0 X1))) (σ X2)
       grind)
    | exact superpose eq853 eq171164
    | exact resolve eq171164 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171164
  have eq171796 : ∀ X0 X1 X2 : G, (σ (M.op X2 (M.op X2 X2))) = (M.op (M.op X1 (M.op X0 (M.op X0 X1))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171520 X0 X1 X2
       have i₂ := eq853 X0 (M.op X0 X1) X1 (σ X2)
       grind)
    | (have i₁ := eq171520 X0 X1 X2
       have i₂ := eq853 X0 X1 (M.op X0 X1) (σ X2)
       grind)
    | exact superpose eq853 eq171520
    | exact resolve eq171520 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq171520
  have eq171993 : ∀ X0 X1 X2 : G, (σ (M.op X2 (M.op X2 X2))) = (M.op X1 (M.op (M.op X0 (M.op X0 X1)) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171796 X0 X1 X2
       have i₂ := eq3453 X1 (M.op X0 (M.op X0 X1)) (σ X2)
       grind)
    | exact superpose eq3453 eq171796
    | exact resolve eq171796 eq3453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3453 eq171796
  have eq172143 : ∀ X0 X1 X2 : G, (σ (M.op X2 (M.op X2 X2))) = (M.op X1 (M.op X0 (M.op X1 (M.op X0 (σ X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq171993 X0 X1 X2
       have i₂ := eq1989 X1 X0 (σ X2) X1 X0
       grind)
    | exact superpose eq1989 eq171993
    | exact resolve eq171993 eq1989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989 eq171993
  have eq172253 : ∀ X0 X2 : G, (σ (M.op X2 (M.op X2 X2))) = (M.op X0 (M.op X0 (σ X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq172143 X0 x X2
       have i₂ := eq993 x X0 (M.op X0 (σ X2))
       grind)
    | (have i₁ := eq172143 X0 X2 X2
       have i₂ := eq993 X0 X2 (M.op X0 (M.op X2 (M.op X0 (σ X2))))
       grind)
    | exact superpose eq993 eq172143
    | exact resolve eq172143 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993 eq172143
  have eq178260 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X2 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq172253 X2 X1
       have i₂ := eq1258 X1 X1 X0
       grind)
    | (have i₁ := eq172253 X2 X1
       have i₂ := eq1258 X0 X1 X1
       grind)
    | exact superpose eq1258 eq172253
    | exact resolve eq172253 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq178566 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (τ (M.op X0 (M.op X0 (σ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 (M.op X1 X1))
       have i₂ := eq172253 X0 X1
       grind)
    | exact superpose eq172253 eq10
    | exact resolve eq10 eq172253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172253
  have eq214193 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ X0) (τ X0))) = (τ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq178566 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq178566
    | exact resolve eq178566 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214432 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (τ (M.op X0 (M.op X0 (σ X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq728 X1 X1 X2
       have i₂ := eq178566 X0 X1
       grind)
    | exact superpose eq178566 eq728
    | exact resolve eq728 eq178566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq215108 : ∀ X0 X1 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq214193 X0 X1
       have i₂ := eq5103 X0 (τ X0)
       grind)
    | exact superpose eq5103 eq214193
    | exact resolve eq214193 eq5103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5103 eq214193
  have eq215516 : ∀ X0 X1 : G, (τ (M.op X1 (M.op X1 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq215108 X0 X1
       have i₂ := eq118817 X0 X0
       grind)
    | exact superpose eq118817 eq215108
    | exact resolve eq215108 eq118817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118817 eq215108
  have eq305754 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq105 X0
       have i₂ := eq57557 X1 X0 X0
       grind)
    | exact superpose eq57557 eq105
    | (have j1 := eq57557 X1 X0 X0
       grind)
    | exact resolve eq105 eq57557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq57557
  have eq305755 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq305754 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305754
  have eq305777 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X2) = (M.op X1 (M.op X1 X2)) ∨ (σ (k X3 X0)) = (σ (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq510 X1 X2 X0
       have i₂ := eq305755 X0 X3
       grind)
    | exact superpose eq305755 eq510
    | (have j1 := eq305755 X0 X3
       grind)
    | exact resolve eq510 eq305755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510 eq305755
  have eq319733 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X1 (M.op X1 X0)) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq7110 x y X0 X1
       grind)
    | exact superpose eq7110 eq16
    | (have j1 := eq7110 x X1 X0 X1
       grind)
    | exact resolve eq16 eq7110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7110
  have eq319845 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (σ x) X0) := by
    intro X0 X1
    first
    | (have j0 := eq319733 X0 X1
       have j1 := eq305777 x X1 X0 x
       grind)
    | (have r₁ := eq319733 X0 X1
       have r₂ := eq305777 x X1 x y
       grind)
    | exact resolve eq319733 eq305777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305777 eq319733
  have eq320268 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1339 X1 X1 X0
       have i₂ := eq319845 X0 X1
       grind)
    | exact superpose eq319845 eq1339
    | exact resolve eq1339 eq319845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320304 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1339 x X0 X1
       have i₂ := eq319845 (M.op X0 X1) x
       grind)
    | exact superpose eq319845 eq1339
    | exact resolve eq1339 eq319845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339
  have eq320341 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (τ (M.op (σ x) (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq214432 x X0 X1
       have i₂ := eq319845 (σ X0) x
       grind)
    | exact superpose eq319845 eq214432
    | exact resolve eq214432 eq319845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214432
  have eq321985 : ∀ X0 : G, (τ (M.op (σ X0) (σ x))) = (M.op X0 (τ (M.op (σ x) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq16034 X0 (σ x)
       have i₂ := eq320268 (σ x) (σ X0)
       grind)
    | exact superpose eq320268 eq16034
    | exact resolve eq16034 eq320268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16034
  have eq322074 : ∀ X0 : G, (τ (M.op (σ X0) (σ x))) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq321985 X0
       have i₂ := eq320341 x X0
       grind)
    | exact superpose eq320341 eq321985
    | exact resolve eq321985 eq320341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320341 eq321985
  have eq323100 : ∀ X0 : G, (τ (M.op X0 (M.op X0 (σ x)))) = (τ (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq215516 (σ x) X0
       have i₂ := eq320304 (σ x) (σ x)
       grind)
    | exact superpose eq320304 eq215516
    | exact resolve eq215516 eq320304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215516 eq320304
  have eq323423 : ∀ X0 : G, (M.op x x) = (τ (M.op X0 (M.op X0 (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq323100 X0
       have i₂ := eq322074 x
       grind)
    | exact superpose eq322074 eq323100
    | exact resolve eq323100 eq322074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322074 eq323100
  have eq323498 : (M.op x x) = (M.op x (M.op x x)) := by
    first
    | (have i₁ := eq323423 x
       have i₂ := eq178566 x x
       grind)
    | exact superpose eq178566 eq323423
    | exact resolve eq323423 eq178566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178566 eq323423
  have eq323524 : (M.op x x) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq323498
       have i₂ := eq319845 x x
       grind)
    | exact superpose eq319845 eq323498
    | exact resolve eq323498 eq319845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323498
  have eq323743 : ∀ X0 : G, (M.op x X0) = (M.op (σ x) (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1437 x X0 (σ x)
       have i₂ := eq323524
       grind)
    | exact superpose eq323524 eq1437
    | exact resolve eq1437 eq323524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437 eq323524
  have eq323865 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq323743 X0
       have i₂ := eq1443 (σ x) X0 x
       grind)
    | (have i₁ := eq323743 X0
       have i₂ := eq1443 (σ x) (M.op (M.op x x) X0) x
       grind)
    | exact superpose eq1443 eq323743
    | exact resolve eq323743 eq1443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1443 eq323743
  have eq326978 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq323865 (σ y)
       grind)
    | exact superpose eq323865 eq16
    | exact resolve eq16 eq323865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327359 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X1 X0))) = (M.op x (M.op (σ x) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq178260 X1 X0 (σ x)
       have i₂ := eq323865 (M.op (σ x) (σ X0))
       grind)
    | exact superpose eq323865 eq178260
    | exact resolve eq178260 eq323865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178260
  have eq327465 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X1 X0))) = (M.op x (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq327359 X0 X1
       have i₂ := eq320268 (σ X0) x
       grind)
    | exact superpose eq320268 eq327359
    | exact resolve eq327359 eq320268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320268 eq327359
  have eq327879 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq327465 X0 x
       have i₂ := eq319845 X0 x
       grind)
    | exact superpose eq319845 eq327465
    | exact resolve eq327465 eq319845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319845 eq327465
  have eq328132 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq327879 X0
       have i₂ := eq323865 X0
       grind)
    | exact superpose eq323865 eq327879
    | exact resolve eq327879 eq323865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323865 eq327879
  have eq337971 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq326978
       have i₂ := eq328132 y
       grind)
    | exact superpose eq328132 eq326978
    | (have r₁ := eq326978
       have r₂ := eq328132 y
       grind)
    | exact resolve eq326978 eq328132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326978 eq328132
  have eq338079 : False := by grind
  exact eq338079

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_y_pxy_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X1 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq25 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 x
       have i₂ := eq26 (M.op X0 X1) X0 x
       grind)
    | exact superpose eq26 eq9
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq68 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq71 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq30 (τ X0) (τ X0)
       grind)
    | exact superpose eq30 eq63
    | exact resolve eq63 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq91 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq110 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq148 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq111 X0 (τ X1)
       grind)
    | exact superpose eq111 eq19
    | (have j1 := eq111 X0 (τ X1)
       grind)
    | exact resolve eq19 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq111 (σ X0) (σ X1)
       grind)
    | exact superpose eq111 eq15
    | (have j1 := eq111 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X0)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 X2
       have i₂ := eq111 X0 X1
       grind)
    | (have i₁ := eq9 X0 X0 X2
       have i₂ := eq111 X0 X1
       grind)
    | exact superpose eq111 eq9
    | (have j1 := eq111 X0 X1
       grind)
    | exact resolve eq9 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq171 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 X1 x
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq160
    | (have j0 := eq160 X0 X1 x
       grind)
    | exact resolve eq160 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq182 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq186 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq194 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq30 (σ X0) (σ X0)
       grind)
    | exact superpose eq30 eq186
    | exact resolve eq186 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq469 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq473 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq469 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq660 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq473 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq473
    | exact resolve eq473 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X1
       have i₂ := eq473 (σ X0) X1
       grind)
    | exact superpose eq473 eq68
    | (have j1 := eq473 (σ X0) X1
       grind)
    | exact resolve eq68 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq473 (τ X0) X1
       grind)
    | exact superpose eq473 eq18
    | (have j1 := eq473 (τ X0) X1
       grind)
    | exact resolve eq18 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq473 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq670 X2 (M.op X0 X1)
       have i₂ := eq26 X0 X1 X2
       grind)
    | exact superpose eq26 eq670
    | (have j0 := eq670 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq670 x (M.op X0 X1)
       have r₂ := eq26 X0 X1 x
       grind)
    | exact resolve eq670 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq770 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq888 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (k X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X2 (M.op X0 X1)
       have i₂ := eq771 X0 X1 (σ X2)
       grind)
    | exact superpose eq771 eq68
    | exact resolve eq68 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq889 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (M.op X0 X1)
       have i₂ := eq771 X0 X1 (τ X2)
       grind)
    | exact superpose eq771 eq18
    | exact resolve eq18 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq980 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) (τ (M.op X0 X1))) := by
    intro X0 X1
    grind
  clear eq888
  have eq986 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq980 X0 X1
       have i₂ := eq30 (τ (M.op X0 X1)) (τ (M.op X0 X1))
       grind)
    | exact superpose eq30 eq980
    | exact resolve eq980 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq980
  have eq1220 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) (σ (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq1226 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1220 X0 X1
       have i₂ := eq30 (σ (M.op X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact superpose eq30 eq1220
    | exact resolve eq1220 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq2852 : ∀ X0 : G, (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq23 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq23
    | exact resolve eq23 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq2862 : ∀ X0 : G, (M.op (τ (σ X0)) (τ (σ X0))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq2852 X0
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq2852
    | exact resolve eq2852 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq2887 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2862 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2862
    | exact resolve eq2862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq3216 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) ≠ (M.op (τ (M.op X0 X1)) X2) ∨ (M.op X2 X2) = (τ (M.op X0 X1)) ∨ (k (τ (M.op X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (τ (M.op X0 X1)) X2
       have i₂ := eq986 X0 X1
       grind)
    | exact superpose eq986 eq13
    | (have j0 := eq13 (τ (M.op X0 X1)) X2
       grind)
    | exact resolve eq13 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3234 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
       have i₂ := eq986 X0 X1
       grind)
    | exact superpose eq986 eq26
    | exact resolve eq26 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq4010 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq1226 X0 X1
       grind)
    | exact superpose eq1226 eq26
    | exact resolve eq26 eq1226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq4086 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq148
    | exact resolve eq148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq4270 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4086 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4086
    | (have j0 := eq4086 X0 X1
       grind)
    | exact resolve eq4086 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086
  have eq6566 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) ∨ (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq194 X0
       have i₂ := eq110 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact superpose eq110 eq194
    | (have j1 := eq110 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq194 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq6585 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) ∨ (M.op (τ (M.op (σ X0) (σ X0))) X0) = (M.op X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq171 (τ (M.op (σ X0) (σ X0))) X0
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq171
    | (have j0 := eq171 (τ (M.op (σ X0) (σ X0))) X0
       grind)
    | exact resolve eq171 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq6615 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) ∨ (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq6585 X0
       have i₂ := eq3234 (σ X0) (σ X0) X0
       grind)
    | exact superpose eq3234 eq6585
    | (have j0 := eq6585 X0
       grind)
    | exact resolve eq6585 eq3234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6585
  have eq6616 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have j0 := eq6615 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6615
  have eq6632 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq6566 X0
       have j1 := eq3216 (σ X0) (σ X0) X0
       grind)
    | (have r₁ := eq6566 x
       have r₂ := eq3216 (σ x) (σ x) x
       grind)
    | exact resolve eq6566 eq3216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3216 eq6566
  have eq6648 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (τ (M.op (σ X0) (σ X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq6632 X0
       have i₂ := eq194 X0
       grind)
    | exact superpose eq194 eq6632
    | (have j0 := eq6632 X0
       grind)
    | exact resolve eq6632 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq6632
  have eq7705 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq149 x y
       grind)
    | exact superpose eq149 eq16
    | (have j1 := eq149 x y
       grind)
    | exact resolve eq16 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7810 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq12449 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq667 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq667
    | exact resolve eq667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq12546 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12449 X0 X1
       have i₂ := eq182 X1 X0
       grind)
    | exact superpose eq182 eq12449
    | (have j0 := eq12449 X0 X1
       grind)
    | exact resolve eq12449 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12449
  have eq12860 : ∀ X0 X1 : G, (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) = (k (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (k X0 X1)
       have i₂ := eq12546 X0 X1
       grind)
    | exact superpose eq12546 eq71
    | (have j1 := eq12546 X0 X1
       grind)
    | exact resolve eq71 eq12546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12546
  have eq12885 : ∀ X0 X1 : G, (σ (τ (M.op X0 X1))) = (k (σ (τ (M.op X0 X1))) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12860 X0 X1
       have i₂ := eq3234 X0 X1 (τ (M.op X0 X1))
       grind)
    | exact superpose eq3234 eq12860
    | (have j0 := eq12860 X0 X1
       grind)
    | exact resolve eq12860 eq3234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12860
  have eq12898 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12885 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq12885
    | (have j0 := eq12885 X0 X1
       grind)
    | exact resolve eq12885 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12885
  have eq14683 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq668 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq668
    | exact resolve eq668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq14830 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14683 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14683
    | (have j0 := eq14683 X0 X1
       grind)
    | exact resolve eq14683 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14683
  have eq15576 : ∀ X0 X1 : G, (τ (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1)))) = (M.op (τ (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1)))) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6616 (k X0 X1)
       have i₂ := eq14830 X0 X1
       grind)
    | exact superpose eq14830 eq6616
    | (have j1 := eq14830 X0 X1
       grind)
    | exact resolve eq6616 eq14830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6616
  have eq15578 : ∀ X0 X1 : G, (τ (σ (M.op X0 X1))) = (M.op (τ (σ (M.op X0 X1))) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15576 X0 X1
       have i₂ := eq4010 X0 X1 (σ (M.op X0 X1))
       grind)
    | exact superpose eq4010 eq15576
    | (have j0 := eq15576 X0 X1
       grind)
    | exact resolve eq15576 eq4010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15576
  have eq15611 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15578 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq15578
    | (have j0 := eq15578 X0 X1
       grind)
    | exact resolve eq15578 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15578
  have eq28805 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (k (M.op X0 X1) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq670 (M.op X0 X1) (k X0 X1)
       have i₂ := eq15611 X0 X1
       grind)
    | exact superpose eq15611 eq670
    | (have j0 := eq670 (M.op X0 X1) (k X0 X1)
       have j1 := eq15611 (M.op X0 X1) (k X0 X1)
       grind)
    | exact resolve eq670 eq15611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15611
  have eq28831 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op X0 X1) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28805 X0 X1
       have j1 := eq473 (M.op X0 X1) (k X0 X1)
       grind)
    | (have r₁ := eq28805 X0 X1
       have r₂ := eq473 X0 X1
       grind)
    | exact resolve eq28805 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28805
  have eq34146 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq660 x y
       grind)
    | exact superpose eq660 eq16
    | (have j1 := eq660 x y
       grind)
    | exact resolve eq16 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq35450 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq34146
       have i₂ := eq4270 y x
       grind)
    | exact superpose eq4270 eq34146
    | (have j1 := eq4270 y x
       grind)
    | (have r₁ := eq34146
       have r₂ := eq4270 y x
       grind)
    | exact resolve eq34146 eq4270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4270
  have eq35451 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq34146
       have i₂ := eq14830 x y
       grind)
    | exact superpose eq14830 eq34146
    | (have j1 := eq14830 x y
       grind)
    | (have r₁ := eq34146
       have r₂ := eq14830 x y
       grind)
    | exact resolve eq34146 eq14830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14830 eq34146
  have eq35453 : (σ (M.op x y)) = (σ y) ∨ y = (k x y) := by grind
  clear eq35451
  have eq35454 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq35450
  have eq35712 : (M.op x y) = (τ (σ y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq35453
       grind)
    | exact superpose eq35453 eq10
    | exact resolve eq10 eq35453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35453
  have eq35795 : y = (M.op x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq35712
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq35712
    | exact resolve eq35712 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35712
  have eq35807 : y = (k x y) := by
    first
    | (have j1 := eq670 x y
       grind)
    | (have r₁ := eq35795
       have r₂ := eq670 x y
       grind)
    | exact resolve eq35795 eq670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670 eq35795
  have eq47195 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq4010 x y x
       have i₂ := eq35454
       grind)
    | exact superpose eq35454 eq4010
    | exact resolve eq4010 eq35454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4010
  have eq101738 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47195 (σ x)
       grind)
    | exact superpose eq47195 eq16
    | exact resolve eq16 eq47195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47195
  have eq101777 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq101738
       have r₂ := eq35454
       grind)
    | exact resolve eq101738 eq35454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35454 eq101738
  have eq104445 : (M.op y x) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq30 x y
       have i₂ := eq101777
       grind)
    | exact superpose eq101777 eq30
    | exact resolve eq30 eq101777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104511 : (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq104445
       have i₂ := eq30 x x
       grind)
    | exact superpose eq30 eq104445
    | exact resolve eq104445 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq104445
  have eq107435 : (M.op x x) = (k (M.op x x) (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12898 y x
       have i₂ := eq104511
       grind)
    | exact superpose eq104511 eq12898
    | (have j0 := eq12898 y x
       grind)
    | exact resolve eq12898 eq104511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12898 eq104511
  have eq140264 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7810 (τ X1) (τ X0)
       have i₂ := eq182 X0 X1
       grind)
    | exact superpose eq182 eq7810
    | exact resolve eq7810 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq7810
  have eq140339 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq140264 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140264
    | (have j0 := eq140264 X0 X1
       grind)
    | exact resolve eq140264 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140264
  have eq140349 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq140339 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq140339
    | (have j0 := eq140339 X0 X1
       grind)
    | exact resolve eq140339 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140339
  have eq140356 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140349 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq140349
    | (have j0 := eq140349 X0 X1
       grind)
    | exact resolve eq140349 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140349
  have eq140358 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq140356 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq140356
    | (have j0 := eq140356 X0 X1
       grind)
    | exact resolve eq140356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140356
  have eq140359 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq140358 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq140358
    | (have j0 := eq140358 X0 X1
       grind)
    | exact resolve eq140358 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140358
  have eq140398 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X0 X1) = (M.op (M.op X0 X1) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140359 (M.op X0 X1) (k X0 X1)
       have i₂ := eq28831 X0 X1
       grind)
    | exact superpose eq28831 eq140359
    | (have j1 := eq28831 X0 X1
       grind)
    | (have r₁ := eq140359 X0 (M.op X0 X0)
       have r₂ := eq28831 X0 (M.op X0 X0)
       grind)
    | exact resolve eq140359 eq28831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28831 eq140359
  have eq140526 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op (M.op X0 X1) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq140398 X0 X1
       have i₂ := eq26 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq26 eq140398
    | (have j0 := eq140398 X0 X1
       grind)
    | exact resolve eq140398 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq140398
  have eq140528 : ∀ X0 X1 : G, (k X0 X1) = (M.op (M.op X0 X1) (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq140526 X0 X1
       have j1 := eq473 X0 X1
       grind)
    | (have r₁ := eq140526 X0 X1
       have r₂ := eq473 X0 X1
       grind)
    | exact resolve eq140526 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq140526
  have eq147674 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (k X2 (σ (k X0 X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq889 (M.op X0 X1) (k X0 X1) X2
       have i₂ := eq140528 X0 X1
       grind)
    | exact superpose eq140528 eq889
    | (have j1 := eq140528 X2 (σ (k X0 X1))
       grind)
    | exact resolve eq889 eq140528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq140528
  have eq152595 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (k X2 (k X0 X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 X1)
       have i₂ := eq147674 X0 X1 (σ X2)
       grind)
    | exact superpose eq147674 eq15
    | (have j1 := eq147674 X0 X1 X2
       grind)
    | exact resolve eq15 eq147674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147674
  have eq170171 : (σ (k y x)) = (σ (M.op x x)) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq152595 y x (M.op x x)
       have i₂ := eq107435
       grind)
    | exact superpose eq107435 eq152595
    | (have j0 := eq152595 y x x
       grind)
    | exact resolve eq152595 eq107435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107435 eq152595
  have eq170210 : (σ (k y x)) = (σ (M.op x x)) ∨ x = (k y x) := by grind
  clear eq170171
  have eq190554 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X0))
       have i₂ := eq6648 X0
       grind)
    | exact superpose eq6648 eq11
    | (have j1 := eq6648 X0
       grind)
    | exact resolve eq11 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6648
  have eq232660 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ (M.op X0 X0)) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 (M.op (σ X0) (σ X0))
       have i₂ := eq190554 X0
       grind)
    | exact superpose eq190554 eq71
    | (have j1 := eq190554 X0
       grind)
    | exact resolve eq71 eq190554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq190554
  have eq232701 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq232660 X0
       have i₂ := eq771 (σ X0) (σ X0) (σ (M.op X0 X0))
       grind)
    | exact superpose eq771 eq232660
    | (have j0 := eq232660 X0
       grind)
    | exact resolve eq232660 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq232660
  have eq232702 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq232701 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232701
  have eq232934 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq7705
       have i₂ := eq232702 x
       grind)
    | exact superpose eq232702 eq7705
    | exact resolve eq7705 eq232702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7705
  have eq233197 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq232934
       have i₂ := eq101777
       grind)
    | exact superpose eq101777 eq232934
    | exact resolve eq232934 eq101777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232934
  have eq233198 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq233197
  have eq233275 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq233198
       have i₂ := eq35807
       grind)
    | exact superpose eq35807 eq233198
    | exact resolve eq233198 eq35807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35807 eq233198
  have eq233324 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq233275
       grind)
    | exact superpose eq233275 eq16
    | exact resolve eq16 eq233275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233416 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3234 (σ x) (σ y) x
       have i₂ := eq233275
       grind)
    | exact superpose eq233275 eq3234
    | exact resolve eq3234 eq233275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3234 eq233275
  have eq233513 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq233416 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq233416
    | exact resolve eq233416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233416
  have eq233555 : (σ y) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq233324
       have i₂ := eq101777
       grind)
    | exact superpose eq101777 eq233324
    | exact resolve eq233324 eq101777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233324
  have eq234193 : y = (M.op x x) := by
    first
    | (have i₁ := eq101777
       have i₂ := eq233513 x
       grind)
    | exact superpose eq233513 eq101777
    | exact resolve eq101777 eq233513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101777 eq233513
  have eq234854 : y = (k y x) := by
    first
    | (have i₁ := eq2887 x
       have i₂ := eq234193
       grind)
    | exact superpose eq234193 eq2887
    | exact resolve eq2887 eq234193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2887 eq234193
  have eq235134 : (σ y) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq170210
       have i₂ := eq234854
       grind)
    | exact superpose eq234854 eq170210
    | exact resolve eq170210 eq234854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170210 eq234854
  have eq235359 : x = y := by
    first
    | (have r₁ := eq235134
       have r₂ := eq233555
       grind)
    | exact resolve eq235134 eq233555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233555 eq235134
  have eq236267 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq235359
       grind)
    | exact superpose eq235359 eq16
    | exact resolve eq16 eq235359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235359
  have eq236331 : False := by grind
  exact eq236331
