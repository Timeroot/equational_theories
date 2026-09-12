import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3964`: `x ◇ y = (y ◇ (y ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_x_pyx_Equation3964 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3964 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3964.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = (M.op X0 X0) := by
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
  have eq40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq47 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq40 (τ X0)
       grind)
    | exact superpose eq40 eq19
    | exact resolve eq19 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq48 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq47 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47
    | exact resolve eq47 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq45 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq45
    | exact resolve eq45 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq48
    | exact resolve eq48 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq48
  have eq67 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq50 X1
       grind)
    | exact superpose eq50 eq67
    | (have j0 := eq67 X0 X1
       grind)
    | exact resolve eq67 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq98 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74
    | (have j0 := eq74 (τ X0) X1
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq403 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq394 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq394
    | (have j0 := eq394 X0 X1
       grind)
    | exact resolve eq394 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq409 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq403
    | (have j0 := eq403 X0 X1
       grind)
    | exact resolve eq403 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq403
  have eq413 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq409 X0 X1
       have j1 := eq98 X1 X0
       grind)
    | (have r₁ := eq409 X1 X0
       have r₂ := eq98 X0 X1
       grind)
    | (have r₁ := eq409 (M.op X1 X1) (M.op X0 X0)
       have r₂ := eq98 X0 X1
       grind)
    | exact resolve eq409 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq409
  have eq418 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq413 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq413
    | exact resolve eq413 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq413 (σ X1) X0
       grind)
    | exact superpose eq413 eq15
    | (have j1 := eq413 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq436 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq418 X0 (τ X1)
       grind)
    | exact superpose eq418 eq18
    | (have j1 := eq418 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq418
  have eq772 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq436 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq436
    | exact resolve eq436 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq809 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq772
    | (have j0 := eq772 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq772 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq2068 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq424 x y
       grind)
    | exact superpose eq424 eq16
    | (have j1 := eq424 x y
       grind)
    | exact resolve eq16 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq2088 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2068
       have i₂ := eq809 y x
       grind)
    | exact superpose eq809 eq2068
    | (have j1 := eq809 (σ x) (σ y)
       grind)
    | (have r₁ := eq2068
       have r₂ := eq809 y x
       grind)
    | (have r₁ := eq2068
       have r₂ := eq809 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2068
       have r₂ := eq809 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2068 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq2068
  have eq2089 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2088
  have eq2180 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2089
       grind)
    | exact superpose eq2089 eq10
    | exact resolve eq10 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq2226 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2180
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2180
    | exact resolve eq2180 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2180
  have eq2227 : x = y := by grind
  clear eq2226
  have eq2229 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2227
       grind)
    | exact superpose eq2227 eq16
    | exact resolve eq16 eq2227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq2230 : False := by grind
  exact eq2230

/-- `Equation4076`: `x ◇ x = ((x ◇ y) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation4076 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4076 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4076.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : x ≠ (M.op x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
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
  have eq68 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq103 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq128 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq145 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq610
    | exact resolve eq610 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq614 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq611
       have r₂ := eq27
       grind)
    | exact resolve eq611 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq616 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq614
    | exact resolve eq614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq618 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq616
    | exact resolve eq616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq622 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq618 eq51
    | (have r₁ := eq51
       have r₂ := eq618
       grind)
    | exact resolve eq51 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq625 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq622
  have eq695 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq625 eq55
    | exact resolve eq55 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq703 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq695
    | exact resolve eq695 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq695
  have eq707 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq703
       have r₂ := eq50
       grind)
    | exact resolve eq703 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq710 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq707
       grind)
    | exact superpose eq707 eq44
    | exact resolve eq44 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq707
       grind)
    | exact superpose eq707 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq712 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq711
  have eq714 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq712
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq712
    | exact resolve eq712 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq715 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq714
  have eq716 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq710
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq710
    | exact resolve eq710 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq719 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq715
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq715
    | exact resolve eq715 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq722 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq719 eq27
    | exact resolve eq27 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq719 eq51
    | exact resolve eq51 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq725 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq719 eq68
    | (have r₁ := eq68
       have r₂ := eq719
       grind)
    | exact resolve eq68 eq719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq719
  have eq727 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq725
  have eq805 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq716 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq806 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq805
  have eq810 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq806
    | exact resolve eq806 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq811 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq810
  have eq816 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq811
    | exact resolve eq811 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq818 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq816 eq27
    | exact resolve eq27 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq834 : (τ (σ y)) = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727 eq55
    | exact resolve eq55 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq727
  have eq845 : y = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq834
    | exact resolve eq834 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq834
  have eq850 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq845
       have r₂ := eq67
       grind)
    | exact resolve eq845 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq858 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq850
       grind)
    | exact superpose eq850 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq859 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq858
  have eq861 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq859
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq859
    | exact resolve eq859 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq859
  have eq862 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq861
  have eq867 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq862
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq862
    | exact resolve eq862 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq862
  have eq917 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq867 eq104
    | exact resolve eq104 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq925 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq867 eq723
    | (have r₁ := eq723
       have r₂ := eq867
       grind)
    | exact resolve eq723 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq867
  have eq931 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq925
  have eq932 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq931
  have eq938 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq917
  have eq1198 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq938 eq932
    | exact resolve eq932 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932 eq938
  have eq1202 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1198
  have eq1206 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1202
       have r₂ := eq722
       grind)
    | exact resolve eq1202 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722 eq1202
  have eq1208 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1206 eq20
    | exact resolve eq20 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1210 : y ≠ y ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1206 eq50
    | (have r₁ := eq50
       have r₂ := eq1206
       grind)
    | exact resolve eq50 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206
  have eq1222 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1210
  have eq1232 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1208
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1208
    | exact resolve eq1208 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1279 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1232 eq26
    | exact resolve eq26 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1232 eq818
    | (have r₁ := eq818
       have r₂ := eq1232
       grind)
    | exact resolve eq818 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq1301 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1295
  have eq1302 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1301
  have eq1322 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1302 eq27
    | exact resolve eq27 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1383 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1222
       grind)
    | exact superpose eq1222 eq44
    | exact resolve eq44 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1389 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1383
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1383
    | exact resolve eq1383 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383
  have eq1398 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1279 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1279
       grind)
    | exact resolve eq12 eq1279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq1401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1398
       have r₂ := eq1302
       grind)
    | exact resolve eq1398 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302 eq1398
  have eq1402 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1401
       have r₂ := eq27
       grind)
    | exact resolve eq1401 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1449 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1232 eq1389
    | exact resolve eq1389 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232 eq1389
  have eq1471 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq1449
  have eq1486 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1471 eq1402
    | exact resolve eq1402 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1402 eq1471
  have eq1490 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1486
  have eq1494 : x = (M.op x y) := by
    first
    | (have r₁ := eq1490
       have r₂ := eq1322
       grind)
    | exact resolve eq1490 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322 eq1490
  have eq1544 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1494 eq20
    | exact resolve eq20 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1546 : x ≠ y ∨ x = (k x y) := by
    first
    | exact superpose eq1494 eq50
    | exact resolve eq50 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1548 : x ≠ x ∨ x = y ∨ y = (k x y) := by
    first
    | exact superpose eq1494 eq67
    | (have r₁ := eq67
       have r₂ := eq1494
       grind)
    | exact resolve eq67 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1559 : y = (k x y) ∨ x = y := by grind
  clear eq1548
  have eq1571 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1544
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1544
    | exact resolve eq1544 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1572 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1571 eq26
    | exact resolve eq26 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1767 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44
       have i₂ := eq1559
       grind)
    | exact superpose eq1559 eq44
    | exact resolve eq44 eq1559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1559
  have eq1776 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1571 eq1767
    | exact resolve eq1767 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq1780 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1776
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1776
    | exact resolve eq1776 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776
  have eq1791 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1780 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1792 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by grind
  clear eq1791
  have eq1795 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1572 eq1792
    | exact resolve eq1792 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq1798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1572 eq1795
    | exact resolve eq1795 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq1801 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq1798
       have r₂ := eq27
       grind)
    | exact resolve eq1798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq1806 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq1801 eq27
    | exact resolve eq27 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1807 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1801 eq51
    | (have r₁ := eq51
       have r₂ := eq1801
       grind)
    | exact resolve eq51 eq1801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1801
  have eq1814 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq1807
  have eq1818 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1571 eq1814
    | exact resolve eq1814 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq1965 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1818 eq1780
    | exact resolve eq1780 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1780
  have eq1966 : (τ (σ (M.op x y))) = (k (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq1818 eq145
    | exact resolve eq145 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq1818
  have eq1969 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq1965
  have eq1974 : (τ (σ (M.op x y))) = (k x y) ∨ x = y := by
    first
    | exact superpose eq1494 eq1966
    | exact resolve eq1966 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966
  have eq1975 : x = y := by
    first
    | (have r₁ := eq1969
       have r₂ := eq1806
       grind)
    | exact resolve eq1969 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806 eq1969
  have eq1979 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | exact superpose eq30 eq1974
    | exact resolve eq1974 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1974
  have eq1982 : x = (k x y) ∨ x = y := by
    first
    | exact superpose eq1494 eq1979
    | exact resolve eq1979 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1494 eq1979
  have eq1984 : x = (k x y) := by
    first
    | (have r₁ := eq1982
       have r₂ := eq1546
       grind)
    | exact resolve eq1982 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546 eq1982
  have eq2112 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1975
       grind)
    | exact superpose eq1975 eq24
    | exact resolve eq24 eq1975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2144 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2112
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2112
    | exact resolve eq2112 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112
  have eq2157 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1571 eq2144
    | exact resolve eq2144 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2144
  have eq2182 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2157 eq1572
    | exact resolve eq1572 eq2157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572 eq2157
  have eq2386 : x = (k x x) := by
    first
    | (have i₁ := eq1984
       have i₂ := eq1975
       grind)
    | exact superpose eq1975 eq1984
    | exact resolve eq1984 eq1975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1975 eq1984
  have eq2388 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq2386
       grind)
    | exact superpose eq2386 eq43
    | exact resolve eq43 eq2386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq2386
  have eq2392 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1571 eq2388
    | exact resolve eq2388 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388
  have eq2393 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2392
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2392
    | exact resolve eq2392 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2392
  have eq2394 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1571 eq2393
    | exact resolve eq2393 eq1571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1571 eq2393
  have eq2654 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2394 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq2394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2394
  have eq2655 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2654
  have eq2706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2182 eq2655
    | exact resolve eq2655 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182 eq2655
  have eq2707 : False := by grind
  exact eq2707

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq33 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) ≠ X0 ∨ (k X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 (M.op X0 (M.op X1 X0)))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op X0 (M.op X0 (M.op X1 X0)))
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (M.op X0 (M.op X0 (M.op X1 X0))) = (k X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 (M.op X0 (M.op X1 X0))
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X0 (M.op X1 X0))
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (k X0 (M.op X0 (M.op X1 X0))) ∨ (M.op X0 (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq273 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq274 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq270
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq270
    | exact resolve eq270 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq275 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq271 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq275 X0
       grind)
    | exact superpose eq275 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq275 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq275 X0
       grind)
    | exact resolve eq12 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq278 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq277 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq280 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq278 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq278
    | exact resolve eq278 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq278 (τ X0)
       grind)
    | exact superpose eq278 eq17
    | (have j1 := eq278 (τ X0)
       grind)
    | exact resolve eq17 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq302 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq296 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq296
    | (have j0 := eq296 X0
       grind)
    | exact resolve eq296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq318 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq302 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq302
    | (have j0 := eq302 X0
       grind)
    | exact resolve eq302 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq342 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq273 X0 X1
       grind)
    | exact superpose eq273 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq273 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq273 X0 X1
       grind)
    | exact resolve eq13 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq273 X1 X0
       grind)
    | exact superpose eq273 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq273 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq273 X1 X1
       grind)
    | exact resolve eq12 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq273 (σ y) (σ x)
       grind)
    | exact superpose eq273 eq16
    | (have j1 := eq273 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq344 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq352 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq342 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq353 : (σ x) = (σ (k x y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq349
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq349
    | exact resolve eq349 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq354 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq352 X0 X1
       have j1 := eq351 X0 X1
       grind)
    | (have r₁ := eq352 X0 X1
       have r₂ := eq351 X0 X1
       grind)
    | (have r₁ := eq352 X1 X0
       have r₂ := eq351 X0 X1
       grind)
    | (have r₁ := eq352 X0 X1
       have r₂ := eq351 (k X0 X1) X1
       grind)
    | exact resolve eq352 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq356 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq353
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq353
    | exact resolve eq353 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq368 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq354 X0 (σ X1)
       grind)
    | exact superpose eq354 eq22
    | (have j1 := eq354 X0 (σ X1)
       grind)
    | exact resolve eq22 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (τ X1) = (k X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq354 X0 (τ X1)
       grind)
    | exact superpose eq354 eq18
    | (have j1 := eq354 X0 (τ X1)
       grind)
    | exact resolve eq18 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq318 (σ X0)
       grind)
    | exact superpose eq318 eq28
    | (have j1 := eq318 (σ X0)
       grind)
    | exact resolve eq28 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 : G, (σ (τ X0)) = (k X0 X0) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq11
    | (have j1 := eq318 X0
       grind)
    | exact resolve eq11 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq504 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq502 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq502
    | (have j0 := eq502 X0
       grind)
    | exact resolve eq502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq511 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq494 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq494
    | (have j0 := eq494 X0
       grind)
    | exact resolve eq494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq524 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq511 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq511
    | (have j0 := eq511 X0
       grind)
    | exact resolve eq511 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq535 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq524 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq524
    | (have j0 := eq524 X0
       grind)
    | exact resolve eq524 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq603 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq504 x
       have i₂ := eq354 x x
       grind)
    | exact superpose eq354 eq504
    | (have j0 := eq504 X0
       have j1 := eq354 X0 X0
       grind)
    | exact resolve eq504 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq504 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq504
    | exact resolve eq504 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq621 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (k (τ X0) (τ X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq504 (τ X0)
       grind)
    | exact superpose eq504 eq17
    | (have j1 := eq504 (τ X0)
       grind)
    | exact resolve eq17 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq624 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq603 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq627 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq621 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq621
    | (have j0 := eq621 X0
       grind)
    | exact resolve eq621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq643 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq604 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq604
    | (have j0 := eq604 X0
       grind)
    | exact resolve eq604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq644 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq624 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq624 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq624 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq648 : ∀ X0 : G, (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq627 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq627
    | (have j0 := eq627 X0
       grind)
    | exact resolve eq627 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq714 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq644 (τ X0)
       grind)
    | exact superpose eq644 eq17
    | (have j1 := eq644 (τ X0)
       grind)
    | exact resolve eq17 eq644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq720 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq714 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq714
    | (have j0 := eq714 X0
       grind)
    | exact resolve eq714 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq812 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq643 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq1369 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op X0 X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq648 x
       have i₂ := eq354 x x
       grind)
    | exact superpose eq354 eq648
    | (have j0 := eq648 X0
       have j1 := eq354 X0 X0
       grind)
    | exact resolve eq648 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq648
  have eq1390 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (M.op X0 X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1369 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1410 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1390 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq1390 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq1390 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1875 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1410 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1410
    | (have j0 := eq1410 (σ X0)
       grind)
    | exact resolve eq1410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1923 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1875 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq1875
    | (have j0 := eq1875 X0
       grind)
    | exact resolve eq1875 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq2397 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X0
       have i₂ := eq265 X0 X1
       grind)
    | exact superpose eq265 eq62
    | (have j1 := eq265 X0 X1
       grind)
    | (have r₁ := eq62 X0 X0
       have r₂ := eq265 X0 X1
       grind)
    | (have r₁ := eq62 X1 X1
       have r₂ := eq265 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq62 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2398 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq265 X0 X1
       grind)
    | exact superpose eq265 eq9
    | (have j1 := eq265 X0 X1
       grind)
    | exact resolve eq9 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq2406 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2397 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq3491 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq720 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq720
    | (have j0 := eq720 (σ X0)
       grind)
    | exact resolve eq720 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3554 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3491 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3491
    | (have j0 := eq3491 X0
       grind)
    | exact resolve eq3491 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq3625 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (k (σ X0) (σ X0))) = (σ (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3554 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3554
    | (have j0 := eq3554 (σ X0)
       grind)
    | exact resolve eq3554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3554
  have eq3686 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (σ (k X0 X0))) = (σ (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3625 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3625
    | (have j0 := eq3625 X0
       grind)
    | exact resolve eq3625 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3625
  have eq4650 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq272 X0 X1
       have i₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact superpose eq14 eq272
    | (have j1 := eq14 X1 (M.op X0 X1)
       grind)
    | exact resolve eq272 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq4659 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4650 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4650
  have eq4664 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4659 X1 X0
       have i₂ := eq273 X0 X1
       grind)
    | exact superpose eq273 eq4659
    | (have j1 := eq273 X0 X1
       grind)
    | exact resolve eq4659 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4676 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (k (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4659 (τ X0) (τ X0)
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq4659
    | (have j1 := eq280 X0
       grind)
    | exact resolve eq4659 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq4659
  have eq4688 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (k (τ X0) (τ (k X0 X0))) ∨ (τ X0) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq4676 X0
       have j1 := eq271 (τ X0) (τ (k X0 X0))
       grind)
    | (have r₁ := eq4676 X0
       have r₂ := eq271 (M.op (τ X0) (τ (k X0 X0))) (k (τ X0) (τ (k X0 X0)))
       grind)
    | (have r₁ := eq4676 X0
       have r₂ := eq271 (k (τ X0) (τ (k X0 X0))) (M.op (τ X0) (τ (k X0 X0)))
       grind)
    | (have r₁ := eq4676 X0
       have r₂ := eq271 (τ X0) (M.op (τ X0) (τ (k X0 X0)))
       grind)
    | exact resolve eq4676 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq4676
  have eq4698 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (k X0 X0))) ∨ (M.op (τ X0) (τ (k X0 X0))) = (τ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4688 X0
       have i₂ := eq31 (k X0 X0) X0
       grind)
    | exact superpose eq31 eq4688
    | (have j0 := eq4688 X0
       grind)
    | exact resolve eq4688 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4688
  have eq5520 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (k (σ X0) (σ X0))) = (σ (σ X0)) ∨ (σ (σ (k X0 X0))) = (σ (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq812 (σ X0)
       have i₂ := eq3686 X0
       grind)
    | exact superpose eq3686 eq812
    | (have j0 := eq812 (σ X0)
       have j1 := eq3686 X0
       grind)
    | exact resolve eq812 eq3686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq3686
  have eq5528 : ∀ X0 : G, (σ (σ (k X0 X0))) = (σ (σ X0)) ∨ (σ (σ X0)) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ (k X0 X0))) = (σ (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5520 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq5520
    | (have j0 := eq5520 X0
       grind)
    | exact resolve eq5520 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5520
  have eq5529 : ∀ X0 : G, (σ (σ X0)) ≠ (σ (σ (M.op X0 X0))) ∨ (σ (σ (k X0 X0))) = (σ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5528 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5528
  have eq5583 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (σ (τ (τ X0)))) ∨ (σ (σ (τ (τ X0)))) = (σ (σ (k (τ (τ X0)) (τ (τ X0))))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5529 (τ (τ X0))
       have i₂ := eq720 X0
       grind)
    | exact superpose eq720 eq5529
    | (have j0 := eq5529 (τ (τ X0))
       have j1 := eq720 X0
       grind)
    | exact resolve eq5529 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq5529
  have eq5598 : ∀ X0 : G, (σ (τ X0)) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (σ (τ (τ X0)))) = (σ (σ (k (τ (τ X0)) (τ (τ X0))))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5583 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq5583
    | (have j0 := eq5583 X0
       grind)
    | exact resolve eq5583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5583
  have eq5617 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (σ (σ (τ (τ X0)))) = (σ (σ (k (τ (τ X0)) (τ (τ X0))))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5598 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5598
    | (have j0 := eq5598 X0
       grind)
    | exact resolve eq5598 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5598
  have eq5628 : ∀ X0 : G, (σ (σ (τ (τ X0)))) = (σ (k (σ (τ (τ X0))) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5617 X0
       have i₂ := eq18 (τ X0) (τ (τ X0))
       grind)
    | exact superpose eq18 eq5617
    | (have j0 := eq5617 X0
       grind)
    | exact resolve eq5617 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5617
  have eq5637 : ∀ X0 : G, (σ (σ (τ (τ X0)))) = (k (σ (σ (τ (τ X0)))) X0) ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5628 X0
       have i₂ := eq18 X0 (σ (τ (τ X0)))
       grind)
    | exact superpose eq18 eq5628
    | (have j0 := eq5628 X0
       grind)
    | exact resolve eq5628 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5628
  have eq5644 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5637 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq5637
    | (have j0 := eq5637 X0
       grind)
    | exact resolve eq5637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5637
  have eq5650 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5644 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5644
    | (have j0 := eq5644 X0
       grind)
    | exact resolve eq5644 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5644
  have eq5651 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5650 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5650
  have eq7248 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq274
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq274
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq274 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq7249 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq7248
  have eq21870 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (τ (M.op (σ X0) (σ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq1923 X0
       grind)
    | exact superpose eq1923 eq10
    | (have j1 := eq1923 X0
       grind)
    | exact resolve eq10 eq1923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1923
  have eq21928 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq21870 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21870
    | (have j0 := eq21870 X0
       grind)
    | exact resolve eq21870 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21870
  have eq22055 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq21928 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21928
    | (have j0 := eq21928 (τ X0)
       grind)
    | exact resolve eq21928 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21928
  have eq22218 : ∀ X0 : G, (τ (M.op X0 X0)) = (σ (M.op (τ (τ X0)) (τ (τ X0)))) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22055 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq22055
    | (have j0 := eq22055 X0
       grind)
    | exact resolve eq22055 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22055
  have eq27991 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5651 (τ X0)
       have i₂ := eq22218 X0
       grind)
    | exact superpose eq22218 eq5651
    | (have j0 := eq5651 (τ X0)
       have j1 := eq22218 X0
       grind)
    | exact resolve eq5651 eq22218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5651 eq22218
  have eq28050 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq27991 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq27991
    | (have j0 := eq27991 X0
       grind)
    | exact resolve eq27991 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27991
  have eq28051 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq28050 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28050
  have eq28114 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (τ (k X0 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28051 X0
       have i₂ := eq2398 X0 X1
       grind)
    | exact superpose eq2398 eq28051
    | (have j0 := eq28051 X0
       have j1 := eq2398 X0 X1
       grind)
    | exact resolve eq28051 eq2398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2398 eq28051
  have eq28146 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (τ X0) = (τ (k X0 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28114
  have eq29600 : (σ (M.op x y)) ≠ (σ x) ∨ (τ (σ y)) = (τ (k (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28146 (σ y) (σ x)
       grind)
    | exact superpose eq28146 eq16
    | (have j1 := eq28146 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq28146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28146
  have eq29673 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq29600
       have i₂ := eq22 (σ y) y
       grind)
    | exact superpose eq22 eq29600
    | exact resolve eq29600 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29600
  have eq29683 : y = (k y y) ∨ (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq29673
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq29673
    | exact resolve eq29673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29673
  have eq29694 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq29683
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq29683
    | exact resolve eq29683 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29683
  have eq54821 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq356
       have i₂ := eq273 y x
       grind)
    | exact superpose eq273 eq356
    | (have j1 := eq273 y x
       grind)
    | exact resolve eq356 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273 eq356
  have eq54823 : x = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq54821
  have eq162616 : (σ x) ≠ (σ x) ∨ y = (k y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k y y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq29694
       have i₂ := eq2406 y x
       grind)
    | exact superpose eq2406 eq29694
    | (have j1 := eq2406 y x
       grind)
    | exact resolve eq29694 eq2406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2406
  have eq162627 : (σ x) ≠ (σ x) ∨ y = (k y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq162616
  have eq162628 : (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k y y) := by grind
  clear eq162627
  have eq176919 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq368
    | exact resolve eq368 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq177487 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq176919 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq176919
    | (have j0 := eq176919 X0 X1
       grind)
    | exact resolve eq176919 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176919
  have eq177544 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq177487 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq177487
    | exact resolve eq177487 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177487
  have eq178121 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq177544 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq177544
    | (have j0 := eq177544 X0 X1
       grind)
    | exact resolve eq177544 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177544
  have eq178161 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq369 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq369
    | exact resolve eq369 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq178735 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq178161 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq178161
    | (have j0 := eq178161 X0 X1
       grind)
    | exact resolve eq178161 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178161
  have eq347553 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq4664 X0 X1
       grind)
    | exact superpose eq4664 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq4664 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq4664 X0 X1
       grind)
    | exact resolve eq13 eq4664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4664
  have eq348294 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq347553 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347553
  have eq348466 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq348294 X0 X1
       have j1 := eq351 X1 X0
       grind)
    | (have r₁ := eq348294 X0 X1
       have r₂ := eq351 X0 X1
       grind)
    | (have r₁ := eq348294 X1 X0
       have r₂ := eq351 X0 X1
       grind)
    | (have r₁ := eq348294 X0 X1
       have r₂ := eq351 (k X0 X1) X1
       grind)
    | exact resolve eq348294 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq348294
  have eq351536 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (k (τ X0) (τ (k X0 X0))) ∨ (M.op (τ X0) (τ (k X0 X0))) = (τ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) (τ (k X0 X0))
       have i₂ := eq4698 X0
       grind)
    | exact superpose eq4698 eq12
    | (have j0 := eq12 (τ X0) (τ (k X0 X0))
       have j1 := eq4698 X0
       grind)
    | exact resolve eq12 eq4698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351564 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 (k X0 X0))) ∨ (M.op (τ X0) (τ (k X0 X0))) = (τ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq4698 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4698
  have eq351587 : ∀ X0 : G, (τ X0) = (τ (k X0 (k X0 X0))) ∨ (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ (k X0 X0))) = (τ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq351536 X0
       have i₂ := eq31 (k X0 X0) X0
       grind)
    | exact superpose eq31 eq351536
    | (have j0 := eq351536 X0
       grind)
    | exact resolve eq351536 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351536
  have eq351656 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ (k X0 X0))) = (τ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have j0 := eq351587 X0
       have j1 := eq351564 X0
       grind)
    | (have r₁ := eq351587 X0
       have r₂ := eq351564 X0
       grind)
    | exact resolve eq351587 eq351564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351564 eq351587
  have eq352475 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (M.op (τ (σ X0)) (k X0 (τ (σ X0)))) = (τ (k (σ X0) (k (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq351656 (σ X0)
       have i₂ := eq28 X0 (σ X0)
       grind)
    | exact superpose eq28 eq351656
    | exact resolve eq351656 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq351656
  have eq352740 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op (τ (σ X0)) (k X0 (τ (σ X0)))) = (τ (k (σ X0) (k (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq352475 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq352475
    | (have j0 := eq352475 X0
       grind)
    | exact resolve eq352475 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352475
  have eq352772 : ∀ X0 : G, (M.op (τ (σ X0)) (k X0 (τ (σ X0)))) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq352740 X0
       have i₂ := eq33 X0 (σ X0) (σ X0)
       grind)
    | exact superpose eq33 eq352740
    | (have j0 := eq352740 X0
       grind)
    | exact resolve eq352740 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq352740
  have eq352786 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (k X0 X0)) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq352772 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq352772
    | (have j0 := eq352772 X0
       grind)
    | exact resolve eq352772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352772
  have eq352808 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq352786 X0
       have i₂ := eq535 X0
       grind)
    | exact superpose eq535 eq352786
    | (have j1 := eq535 X0
       grind)
    | (have r₁ := eq352786 X0
       have r₂ := eq535 X0
       grind)
    | exact resolve eq352786 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq352786
  have eq353245 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq352808 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352808
  have eq353692 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq353245 X0
       grind)
    | exact superpose eq353245 eq10
    | (have j1 := eq353245 X0
       grind)
    | exact resolve eq10 eq353245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353245
  have eq353930 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq353692 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq353692
    | (have j0 := eq353692 X0
       grind)
    | exact resolve eq353692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353692
  have eq353931 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq353930 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353930
  have eq354560 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq353931 (σ X0)
       grind)
    | exact superpose eq353931 eq15
    | exact resolve eq15 eq353931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354663 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq354560 X0
       have i₂ := eq353931 X0
       grind)
    | exact superpose eq353931 eq354560
    | exact resolve eq354560 eq353931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354560
  have eq926681 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (σ (k X1 X0)) ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq178121 X1 X0
       grind)
    | exact superpose eq178121 eq10
    | (have j1 := eq178121 X1 X0
       grind)
    | exact resolve eq10 eq178121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178121
  have eq927225 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq926681 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq926681
    | (have j0 := eq926681 X0 X1
       grind)
    | exact resolve eq926681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq926681
  have eq932363 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (k X0 X1))) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq927225 (τ X0) (τ X1)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq927225
    | exact resolve eq927225 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq932530 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq927225 X1 X0
       grind)
    | exact superpose eq927225 eq10
    | (have j1 := eq927225 X1 X0
       grind)
    | exact resolve eq10 eq927225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927225
  have eq932954 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq932530 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq932530
    | (have j0 := eq932530 X0 X1
       grind)
    | exact resolve eq932530 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932530
  have eq933060 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq932363 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq932363
    | (have j0 := eq932363 X0 X1
       grind)
    | exact resolve eq932363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932363
  have eq933433 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq933060 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq933060
    | (have j0 := eq933060 X0 X1
       grind)
    | exact resolve eq933060 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933060
  have eq933695 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X0)) X1)) ∨ (k X0 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq933433 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq933433
    | (have j0 := eq933433 X0 X1
       grind)
    | exact resolve eq933433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933433
  have eq933860 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq933695 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq933695
    | (have j0 := eq933695 X0 X1
       grind)
    | exact resolve eq933695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933695
  have eq934962 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq932954 X0 X1
       grind)
    | exact superpose eq932954 eq11
    | (have j1 := eq932954 X0 X1
       grind)
    | exact resolve eq11 eq932954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932954
  have eq938424 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (τ X0) = (k X1 (τ X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq934962 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq934962
    | (have j0 := eq934962 X1 (τ X0)
       grind)
    | exact resolve eq934962 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq938676 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq934962 x y
       grind)
    | exact superpose eq934962 eq16
    | (have j1 := eq934962 x y
       grind)
    | exact resolve eq16 eq934962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934962
  have eq939851 : y = (k x y) ∨ x = (k x y) := by
    first
    | (have j1 := eq178735 y x
       grind)
    | (have r₁ := eq938676
       have r₂ := eq178735 y x
       grind)
    | exact resolve eq938676 eq178735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178735 eq938676
  have eq940021 : ∀ X0 X1 : G, (τ X0) = (k X1 (τ X0)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq938424 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq938424
    | (have j0 := eq938424 X0 X1
       grind)
    | exact resolve eq938424 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq938424
  have eq942282 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq162628
       have i₂ := eq939851
       grind)
    | exact superpose eq939851 eq162628
    | exact resolve eq162628 eq939851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942283 : x ≠ y ∨ x = (k x y) := by grind
  have eq942285 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 y y
       grind)
    | (have r₁ := eq942282
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq942282
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq942282 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942282
  have eq942290 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq942285
       have i₂ := eq353931 y
       grind)
    | exact superpose eq353931 eq942285
    | exact resolve eq942285 eq353931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942285
  have eq943774 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X1))) ∨ (k X0 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1)
       have i₂ := eq933860 X0 X1
       grind)
    | exact superpose eq933860 eq11
    | (have j1 := eq933860 X0 X1
       grind)
    | exact resolve eq11 eq933860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933860
  have eq944338 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq943774 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq943774
    | (have j0 := eq943774 X0 X1
       grind)
    | exact resolve eq943774 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943774
  have eq946862 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (τ (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq944338 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq944338
    | exact resolve eq944338 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944338
  have eq947748 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = X1 ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq946862 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq946862
    | (have j0 := eq946862 X0 X1
       grind)
    | exact resolve eq946862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946862
  have eq948072 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq947748 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq947748
    | (have j0 := eq947748 X0 X1
       grind)
    | exact resolve eq947748 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947748
  have eq955303 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (τ X0))) ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) ∨ (τ X1) = (k (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq940021 X0 (τ X1)
       grind)
    | exact superpose eq940021 eq17
    | (have j1 := eq940021 X0 (τ X1)
       grind)
    | exact resolve eq17 eq940021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq940021
  have eq955541 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) ∨ (τ X1) = (k (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq955303 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq955303
    | (have j0 := eq955303 X0 X1
       grind)
    | exact resolve eq955303 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955303
  have eq956042 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (τ X1) = (k (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq955541 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq955541
    | (have j0 := eq955541 X0 X1
       grind)
    | exact resolve eq955541 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955541
  have eq956418 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq956042 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq956042
    | (have j0 := eq956042 X0 X1
       grind)
    | exact resolve eq956042 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956042
  have eq957830 : ∀ X0 X1 X2 : G, (k (τ X1) (τ X0)) = (τ (k X1 (k X0 X2))) ∨ (k X0 X2) = (M.op X0 X2) ∨ (k X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X0 X2) X1
       have i₂ := eq956418 X2 X0
       grind)
    | exact superpose eq956418 eq31
    | (have j1 := eq956418 X2 X0
       grind)
    | exact resolve eq31 eq956418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956418
  have eq958399 : ∀ X0 X1 X2 : G, (τ (k X1 X0)) = (τ (k X1 (k X0 X2))) ∨ (k X0 X2) = (M.op X0 X2) ∨ (k X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq957830 X0 X1 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq957830
    | (have j0 := eq957830 X0 X1 X2
       grind)
    | exact resolve eq957830 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq957830
  have eq969302 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq948072 x y
       have i₂ := eq162628
       grind)
    | exact superpose eq162628 eq948072
    | (have j0 := eq948072 y y
       grind)
    | exact resolve eq948072 eq162628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948072
  have eq969878 : y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq969302
       have r₂ := eq29694
       grind)
    | exact resolve eq969302 eq29694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969302
  have eq970221 : y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq969878
       have r₂ := eq16
       grind)
    | exact resolve eq969878 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969878
  have eq970506 : y = (M.op x y) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq970221
       have i₂ := eq353931 y
       grind)
    | exact superpose eq353931 eq970221
    | exact resolve eq970221 eq353931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970221
  have eq971086 : y ≠ y ∨ x = (k x y) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq970506
       grind)
    | exact superpose eq970506 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq970506
       grind)
    | (have r₁ := eq12 y y
       have r₂ := eq970506
       grind)
    | exact resolve eq12 eq970506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970506
  have eq971148 : x = (k x y) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq971086
  have eq971191 : x = (M.op x y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq971148
       have i₂ := eq162628
       grind)
    | exact superpose eq162628 eq971148
    | exact resolve eq971148 eq162628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162628
  have eq971207 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have j1 := eq12 y y
       grind)
    | (have r₁ := eq971191
       have r₂ := eq12 y y
       grind)
    | exact resolve eq971191 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971191
  have eq971208 : x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq971207
       have r₂ := eq16
       grind)
    | exact resolve eq971207 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971207
  have eq971209 : x = (M.op x y) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq971208
       have i₂ := eq353931 y
       grind)
    | exact superpose eq353931 eq971208
    | exact resolve eq971208 eq353931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971208
  have eq971214 : (σ x) ≠ (σ x) ∨ y = (k y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq29694
       have i₂ := eq971209
       grind)
    | exact superpose eq971209 eq29694
    | exact resolve eq29694 eq971209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29694 eq971209
  have eq971265 : (σ x) ≠ (σ x) ∨ y = (k y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op y y) := by grind
  clear eq971214
  have eq971266 : y = (k y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op y y) := by grind
  clear eq971265
  have eq971279 : y = (k y y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have j1 := eq12 y y
       grind)
    | (have r₁ := eq971266
       have r₂ := eq12 y y
       grind)
    | exact resolve eq971266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971266
  have eq971285 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq971279
       have i₂ := eq353931 y
       grind)
    | exact superpose eq353931 eq971279
    | exact resolve eq971279 eq353931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971279
  have eq971316 : (σ x) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq971285
       grind)
    | exact superpose eq971285 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq971285
       grind)
    | exact resolve eq13 eq971285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq971396 : (σ y) = (σ (k x y)) ∨ (σ x) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq971316
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq971316
    | exact resolve eq971316 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971316
  have eq971397 : (σ x) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op y y) := by grind
  clear eq971396
  have eq971585 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq971397
       have i₂ := eq942290
       grind)
    | exact superpose eq942290 eq971397
    | exact resolve eq971397 eq942290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942290
  have eq971595 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq971585
  have eq971596 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq971595
  have eq972397 : (σ y) = (σ (k x y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq971285
       have i₂ := eq971596
       grind)
    | exact superpose eq971596 eq971285
    | exact resolve eq971285 eq971596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971285 eq971596
  have eq972487 : (σ x) = (σ y) ∨ y = (M.op y y) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq972397
  have eq972726 : y = (τ (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq972487
       grind)
    | exact superpose eq972487 eq10
    | exact resolve eq10 eq972487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972487
  have eq973154 : x = y ∨ y = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq972726
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq972726
    | exact resolve eq972726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972726
  have eq973504 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq973154
       grind)
    | exact superpose eq973154 eq16
    | exact resolve eq16 eq973154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973154
  have eq973563 : (σ y) = (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq973504
       have r₂ := eq354663 x
       grind)
    | exact resolve eq973504 eq354663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973504
  have eq973584 : (k x y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq973563
       grind)
    | exact superpose eq973563 eq10
    | exact resolve eq10 eq973563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973563
  have eq974006 : y = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq973584
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq973584
    | exact resolve eq973584 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973584
  have eq974318 : x = y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq971148
       have i₂ := eq974006
       grind)
    | exact superpose eq974006 eq971148
    | exact resolve eq971148 eq974006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971148 eq974006
  have eq974321 : x = y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq974318
  have eq975881 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq974321
       grind)
    | exact superpose eq974321 eq16
    | exact resolve eq16 eq974321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974321
  have eq975956 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq975881
       have r₂ := eq354663 x
       grind)
    | exact resolve eq975881 eq354663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975881
  have eq976002 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq975956
       grind)
    | exact superpose eq975956 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq975956
       grind)
    | (have r₁ := eq12 y y
       have r₂ := eq975956
       grind)
    | exact resolve eq12 eq975956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975956
  have eq976058 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq976002
  have eq976105 : (σ x) = (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq976058
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq976058
    | exact resolve eq976058 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976058
  have eq976263 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq971397
       have i₂ := eq976105
       grind)
    | exact superpose eq976105 eq971397
    | (have r₁ := eq971397
       have r₂ := eq976105
       grind)
    | exact resolve eq971397 eq976105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971397 eq976105
  have eq976513 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq976263
  have eq976514 : (σ x) = (σ y) ∨ y = (M.op y y) := by grind
  clear eq976513
  have eq977003 : y = (τ (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq976514
       grind)
    | exact superpose eq976514 eq10
    | exact resolve eq10 eq976514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976514
  have eq977432 : x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq977003
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq977003
    | exact resolve eq977003 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977003
  have eq977785 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq977432
       grind)
    | exact superpose eq977432 eq16
    | exact resolve eq16 eq977432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977432
  have eq977863 : y = (M.op y y) := by
    first
    | (have r₁ := eq977785
       have r₂ := eq354663 x
       grind)
    | exact resolve eq977785 eq354663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977785
  have eq1115200 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k X0 (k X1 X2)) ∨ (k X1 X2) = (M.op X1 X2) ∨ (k X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X0 (k X1 X2))
       have i₂ := eq958399 X1 X0 X2
       grind)
    | exact superpose eq958399 eq11
    | (have j1 := eq958399 X1 X1 X2
       grind)
    | exact resolve eq11 eq958399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958399
  have eq1115795 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X1 X2) ∨ (k X0 X1) = (k X0 (k X1 X2)) ∨ (k X1 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1115200 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1115200
    | (have j0 := eq1115200 X0 X1 X2
       grind)
    | exact resolve eq1115200 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115200
  have eq1118026 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op x y) ∨ (k X0 (k x y)) = (k X0 x) ∨ y = (k x y) := by
    intro X0
    first
    | (have i₁ := eq939851
       have i₂ := eq1115795 X0 x y
       grind)
    | exact superpose eq1115795 eq939851
    | (have j1 := eq1115795 X0 x y
       grind)
    | exact resolve eq939851 eq1115795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1118071 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (k X2 X0) = (k X2 (k X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1115795 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115795
  have eq1118076 : ∀ X0 : G, y = (M.op x y) ∨ (k X0 (k x y)) = (k X0 x) ∨ y = (k x y) := by
    intro X0
    first
    | (have j0 := eq1118026 X0
       have j1 := eq13 x y
       grind)
    | (have r₁ := eq1118026 X0
       have r₂ := eq13 x y
       grind)
    | exact resolve eq1118026 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118026
  have eq1118396 : ∀ X0 : G, y = (k x y) ∨ (k X0 (k x y)) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq1118076 X0
       have j1 := eq1118071 x y X0
       grind)
    | (have r₁ := eq1118076 X0
       have r₂ := eq1118071 x y x
       grind)
    | exact resolve eq1118076 eq1118071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118071 eq1118076
  have eq3769833 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq54823
       have i₂ := eq939851
       grind)
    | exact superpose eq939851 eq54823
    | exact resolve eq54823 eq939851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54823
  have eq3769914 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq3769833
       have r₂ := eq942283
       grind)
    | exact resolve eq3769833 eq942283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769833
  have eq3769935 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq3769914
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq3769914
       have r₂ := eq12 x y
       grind)
    | exact resolve eq3769914 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769914
  have eq3770006 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq3769935
       grind)
    | exact superpose eq3769935 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3769935
       grind)
    | exact resolve eq12 eq3769935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3769935
  have eq3770123 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (k x y) := by grind
  clear eq3770006
  have eq3770234 : x = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq3770123
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3770123
    | exact resolve eq3770123 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770123
  have eq3770630 : ∀ X0 : G, x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k X0 (k x y)) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq3770234
       have i₂ := eq1118396 X0
       grind)
    | exact superpose eq1118396 eq3770234
    | (have j1 := eq1118396 X0
       grind)
    | exact resolve eq3770234 eq1118396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118396 eq3770234
  have eq3770730 : ∀ X0 : G, x = y ∨ (σ x) = (σ y) ∨ (k X0 (k x y)) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq3770630 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770630
  have eq3770922 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k X0 (k x y)) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq3770730 X0
       grind)
    | exact superpose eq3770730 eq16
    | (have j1 := eq3770730 X0
       grind)
    | exact resolve eq16 eq3770730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770730
  have eq3771217 : ∀ X0 : G, (σ x) = (σ y) ∨ (k X0 (k x y)) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq3770922 X0
       grind)
    | (have r₁ := eq3770922 X0
       have r₂ := eq354663 x
       grind)
    | exact resolve eq3770922 eq354663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770922
  have eq3771249 : ∀ X0 : G, y = (τ (σ x)) ∨ (k X0 (k x y)) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq3771217 X0
       grind)
    | exact superpose eq3771217 eq10
    | (have j1 := eq3771217 X0
       grind)
    | exact resolve eq10 eq3771217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771217
  have eq3772003 : ∀ X0 : G, x = y ∨ (k X0 (k x y)) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq3771249 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3771249
    | (have j0 := eq3771249 X0
       grind)
    | exact resolve eq3771249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3771249
  have eq3772729 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (k x y)) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq3772003 X0
       grind)
    | exact superpose eq3772003 eq16
    | (have j1 := eq3772003 X0
       grind)
    | exact resolve eq16 eq3772003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3772003
  have eq3773024 : ∀ X0 : G, (k X0 (k x y)) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq3772729 X0
       grind)
    | (have r₁ := eq3772729 X0
       have r₂ := eq354663 x
       grind)
    | exact resolve eq3772729 eq354663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3772729
  have eq3774543 : (k (k x y) x) = (M.op (k x y) (k x y)) := by
    first
    | (have i₁ := eq353931 (k x y)
       have i₂ := eq3773024 (k x y)
       grind)
    | exact superpose eq3773024 eq353931
    | exact resolve eq353931 eq3773024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353931 eq3773024
  have eq3793061 : (k y x) = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3774543
       have i₂ := eq939851
       grind)
    | exact superpose eq939851 eq3774543
    | exact resolve eq3774543 eq939851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774543
  have eq3794258 : y = (k y x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq3793061
       have i₂ := eq977863
       grind)
    | exact superpose eq977863 eq3793061
    | exact resolve eq3793061 eq977863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977863 eq3793061
  have eq3794657 : y = (M.op y x) ∨ x = y ∨ x = (k x y) ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq348466 y x
       have i₂ := eq3794258
       grind)
    | exact superpose eq3794258 eq348466
    | (have j0 := eq348466 y x
       grind)
    | exact resolve eq348466 eq3794258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348466
  have eq3794658 : y = (M.op y x) ∨ x = y ∨ x = (k x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq3794657
  have eq3794666 : y = (M.op y x) ∨ x = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq3794658
       have r₂ := eq942283
       grind)
    | exact resolve eq3794658 eq942283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3794658
  have eq4036907 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3794666
       grind)
    | exact superpose eq3794666 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3794666
       grind)
    | exact resolve eq13 eq3794666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3794666
  have eq4037015 : x = y ∨ x = (k y x) ∨ x = (k x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq4036907
  have eq4037030 : x = (k y x) ∨ x = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq4037015
       have r₂ := eq942283
       grind)
    | exact resolve eq4037015 eq942283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4037015
  have eq4147077 : x = y ∨ x = (k x y) ∨ x = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq3794258
       have i₂ := eq4037030
       grind)
    | exact superpose eq4037030 eq3794258
    | exact resolve eq3794258 eq4037030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3794258 eq4037030
  have eq4147080 : x = y ∨ x = (k x y) ∨ (M.op x y) = (k x y) := by grind
  clear eq4147077
  have eq4147091 : x = (k x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have r₁ := eq4147080
       have r₂ := eq942283
       grind)
    | exact resolve eq4147080 eq942283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147080
  have eq4147112 : x = y ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq4147091
       have i₂ := eq939851
       grind)
    | exact superpose eq939851 eq4147091
    | exact resolve eq4147091 eq939851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939851 eq4147091
  have eq4147197 : y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have r₁ := eq4147112
       have r₂ := eq942283
       grind)
    | exact resolve eq4147112 eq942283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942283 eq4147112
  have eq4147218 : x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq4147197
       have r₂ := eq12 x y
       grind)
    | exact resolve eq4147197 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147197
  have eq4147281 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7249
       have i₂ := eq4147218
       grind)
    | exact superpose eq4147218 eq7249
    | exact resolve eq7249 eq4147218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7249
  have eq4147317 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4147281
  have eq4147407 : x ≠ x ∨ x = y ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq4147317
       grind)
    | exact superpose eq4147317 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4147317
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4147317
       grind)
    | exact resolve eq13 eq4147317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147317
  have eq4147491 : x = y ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4147407
  have eq4147513 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4147491
       have i₂ := eq4147218
       grind)
    | exact superpose eq4147218 eq4147491
    | exact resolve eq4147491 eq4147218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147491
  have eq4147514 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq4147513
  have eq4147582 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4147514
       grind)
    | exact superpose eq4147514 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4147514
       grind)
    | exact resolve eq13 eq4147514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147514
  have eq4147666 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = y := by grind
  clear eq4147582
  have eq4147729 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4147666
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4147666
    | exact resolve eq4147666 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147666
  have eq4147775 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq4147729
       have i₂ := eq4147218
       grind)
    | exact superpose eq4147218 eq4147729
    | exact resolve eq4147729 eq4147218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147218 eq4147729
  have eq4147776 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq4147775
  have eq4147816 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4147776
       grind)
    | exact superpose eq4147776 eq16
    | exact resolve eq16 eq4147776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147776
  have eq4148193 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq4147816
       have r₂ := eq354663 x
       grind)
    | exact resolve eq4147816 eq354663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4147816
  have eq4148199 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4148193
       grind)
    | exact superpose eq4148193 eq16
    | exact resolve eq16 eq4148193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4148230 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4148193
       grind)
    | exact superpose eq4148193 eq10
    | exact resolve eq10 eq4148193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148193
  have eq4148984 : x = y := by
    first
    | (have i₁ := eq4148230
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4148230
    | exact resolve eq4148230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148230
  have eq4148995 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4148199
       have i₂ := eq354663 x
       grind)
    | exact superpose eq354663 eq4148199
    | exact resolve eq4148199 eq354663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354663 eq4148199
  have eq4149251 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4148995
       have i₂ := eq4148984
       grind)
    | exact superpose eq4148984 eq4148995
    | exact resolve eq4148995 eq4148984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148984 eq4148995
  have eq4149252 : False := by grind
  exact eq4149252

/-- `Equation4164`: `x ◇ y = ((y ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyy_pyx_pxy_pyx_Equation4164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X1 X1) X0) X0) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq94 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq94
    | (have j0 := eq94 X0 X1
       grind)
    | exact resolve eq94 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq106 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq10
    | exact resolve eq10 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op (M.op (τ (M.op X0 X0)) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq219 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | (have j0 := eq96 (τ X0) X1
       grind)
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq233 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq219 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq219
    | (have j0 := eq219 X0 X1
       grind)
    | exact resolve eq219 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq219
  have eq241 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq233 X1 X0
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq233 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq233
  have eq247 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq241 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq241
    | (have j0 := eq241 X0 X1
       grind)
    | exact resolve eq241 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241
  have eq427 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq247 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq247
    | (have j0 := eq247 X1 (τ X0)
       grind)
    | exact resolve eq247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq454 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq427
    | (have j0 := eq427 X0 X1
       grind)
    | exact resolve eq427 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq427
  have eq484 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) X1) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2
       have i₂ := eq454 X2 X0
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq454 X0 X1
       grind)
    | exact superpose eq454 eq9
    | (have j1 := eq454 X2 X0
       grind)
    | exact resolve eq9 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (M.op X0 X0)) X1) X1) = (M.op X1 (τ X2)) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq147 X2 X1
       have i₂ := eq454 X2 X0
       grind)
    | (have i₁ := eq147 X1 X1
       have i₂ := eq454 X0 X1
       grind)
    | exact superpose eq454 eq147
    | (have j1 := eq454 X2 X0
       grind)
    | exact resolve eq147 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454
  have eq506 : ∀ X0 X1 X2 : G, (M.op X1 (τ X0)) = (M.op X1 (τ X2)) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq491 X0 X1 X2
       have i₂ := eq147 X0 X1
       grind)
    | exact superpose eq147 eq491
    | (have j0 := eq491 X0 X1 X2
       grind)
    | exact resolve eq491 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147 eq491
  have eq508 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X1 X0) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq484 X0 X1 X2
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq484
    | (have j0 := eq484 X0 X1 X2
       grind)
    | exact resolve eq484 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq1006 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (k (σ X0) X2) ∨ (M.op X1 X0) = (M.op X1 (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq506 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq506
    | (have j0 := eq506 (σ X0) X1 X2
       grind)
    | exact resolve eq506 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq2655 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X1) = (M.op X2 (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1006 X1 X2 (σ X0)
       grind)
    | exact superpose eq1006 eq15
    | (have j1 := eq1006 X1 X2 (σ X0)
       grind)
    | exact resolve eq15 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq2685 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2655 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2655
    | (have j0 := eq2655 X0 X1 X2
       grind)
    | exact resolve eq2655 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655
  have eq3613 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2685 x y X0
       grind)
    | exact superpose eq2685 eq16
    | (have j1 := eq2685 x y X0
       grind)
    | exact resolve eq16 eq2685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq3766 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq3613 X0
       have i₂ := eq508 y X1 x
       grind)
    | exact superpose eq508 eq3613
    | (have j0 := eq3613 X0
       have j1 := eq508 y X0 x
       grind)
    | exact resolve eq3613 eq508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508 eq3613
  have eq3779 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 x) ∨ (M.op X1 y) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have j0 := eq3766 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3766
  have eq3833 : ∀ X0 : G, (M.op X0 x) ≠ (M.op X0 x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3779 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3779
  have eq3834 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq3833 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833
  have eq4060 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op X0 X0) y) x) := by
    intro X0
    first
    | (have i₁ := eq9 y X0
       have i₂ := eq3834 (M.op (M.op X0 X0) y)
       grind)
    | exact superpose eq3834 eq9
    | exact resolve eq9 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4099 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op X0 X0) x) x) := by
    intro X0
    first
    | (have i₁ := eq4060 X0
       have i₂ := eq3834 (M.op X0 X0)
       grind)
    | exact superpose eq3834 eq4060
    | exact resolve eq4060 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060
  have eq4134 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq4099 X0
       have i₂ := eq9 x X0
       grind)
    | exact superpose eq9 eq4099
    | exact resolve eq4099 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4099
  have eq4395 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ (M.op x y)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq79 y X0
       have i₂ := eq4134 y
       grind)
    | exact superpose eq4134 eq79
    | exact resolve eq79 eq4134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4134
  have eq4439 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ (M.op x x)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq4395 X0
       have i₂ := eq3834 x
       grind)
    | exact superpose eq3834 eq4395
    | exact resolve eq4395 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4395
  have eq4469 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4439 X0
       have i₂ := eq79 x X0
       grind)
    | exact superpose eq79 eq4439
    | exact resolve eq4439 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq4439
  have eq5320 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4469 (σ x)
       grind)
    | exact superpose eq4469 eq16
    | exact resolve eq16 eq4469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4469
  have eq5353 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5320
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq5320
    | exact resolve eq5320 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5320
  have eq5416 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq5353
       have i₂ := eq3834 x
       grind)
    | exact superpose eq3834 eq5353
    | exact resolve eq5353 eq3834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834 eq5353
  have eq5417 : False := by grind
  exact eq5417

/-- `Equation4277`: `x ◇ (x ◇ x) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then Y else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_y_pxx_pxy_Equation4277 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4277 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4277.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
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
  clear eq36
  have eq49 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq71 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq71
    | exact resolve eq71 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq75
    | exact resolve eq75 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq211 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 x
       have i₂ := eq14 x X0 X1
       grind)
    | (have i₁ := eq49 x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X1 X1)
       have i₂ := eq49 X1
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X1 : G, (M.op x (M.op x y)) = (M.op X1 (M.op x (M.op x y))) := by
    intro X1
    first
    | (have i₁ := eq215 x X1
       have i₂ := eq49 x
       grind)
    | exact superpose eq49 eq215
    | exact resolve eq215 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq217 : (M.op x (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq49 x
       grind)
    | exact superpose eq49 eq50
    | exact resolve eq50 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq731 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq67 X1 X1
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq736 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq731 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq741 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq736 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq736 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq736 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq736 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq753 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq741
    | (have j0 := eq741 X0 X1
       grind)
    | exact resolve eq741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq6427 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq753
  have eq6541 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6427
  have eq6542 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq6541 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6541
  have eq6984 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6542 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6542
    | (have j0 := eq6542 x
       grind)
    | exact resolve eq6542 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6991 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq49 (σ X0)
       have i₂ := eq6542 X0
       grind)
    | exact superpose eq6542 eq49
    | exact resolve eq49 eq6542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq7011 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq6984
       grind)
    | exact superpose eq6984 eq16
    | exact resolve eq16 eq6984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6984
  have eq8423 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq216 eq6991
    | exact resolve eq6991 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8453 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq8423
       have i₂ := eq6542 (M.op x sF0)
       grind)
    | exact superpose eq6542 eq8423
    | exact resolve eq8423 eq6542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6542 eq8423
  have eq8467 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq216 eq8453
    | exact resolve eq8453 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8453
  have eq8474 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq8467 eq16
    | exact resolve eq16 eq8467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq77 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq10986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10985
    | exact resolve eq10985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10985
  have eq10999 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10986
       have r₂ := eq28
       grind)
    | exact resolve eq10986 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10986
  have eq11002 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10999
    | exact resolve eq10999 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10999
  have eq11004 : (τ (σ y)) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11002 eq7011
    | exact resolve eq7011 eq11002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7011 eq11002
  have eq11018 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq11004
    | exact resolve eq11004 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11004
  have eq11019 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11018
  have eq11026 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6991 x
       have i₂ := eq11019
       grind)
    | exact superpose eq11019 eq6991
    | exact resolve eq6991 eq11019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6991
  have eq11030 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq211 x x
       have i₂ := eq11019
       grind)
    | exact superpose eq11019 eq211
    | exact resolve eq211 eq11019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq11019
  have eq11034 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11030
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11030
    | exact resolve eq11030 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11030
  have eq11037 : (M.op x (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11026
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11026
    | exact resolve eq11026 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11026
  have eq11041 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11037
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11037
    | exact resolve eq11037 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq11037
  have eq11042 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11041
    | exact resolve eq11041 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11041
  have eq11237 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11034 eq8467
    | exact resolve eq8467 eq11034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11245 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq11237
    | exact resolve eq11237 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11237
  have eq11247 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11245 eq217
    | exact resolve eq217 eq11245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11250 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11247
    | exact resolve eq11247 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11247
  have eq11590 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11042 eq11034
    | exact resolve eq11034 eq11042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11034 eq11042
  have eq11596 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11590
  have eq11738 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11596 eq217
    | exact resolve eq217 eq11596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq11740 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq11742 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11738
    | exact resolve eq11738 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11738
  have eq12575 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11250 eq216
    | exact resolve eq216 eq11250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12582 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11250 eq8474
    | exact resolve eq8474 eq11250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11250
  have eq12793 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11245 eq12582
    | exact resolve eq12582 eq11245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12582
  have eq12826 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq12793
  have eq12828 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq12826
    | exact resolve eq12826 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12826
  have eq13273 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11742 eq216
    | exact resolve eq216 eq11742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13280 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11742 eq8474
    | exact resolve eq8474 eq11742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8474 eq11742
  have eq13358 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11596 eq13280
    | exact resolve eq13280 eq11596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13280
  have eq13393 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq13358
  have eq13395 : (σ y) = (τ (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq13393
       have r₂ := eq11740
       grind)
    | exact resolve eq13393 eq11740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13393
  have eq13396 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq30 eq13395
    | exact resolve eq13395 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq13395
  have eq13540 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq13396 eq28
    | exact resolve eq28 eq13396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13396
  have eq13560 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq13540
       have r₂ := eq12828
       grind)
    | exact resolve eq13540 eq12828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12828 eq13540
  have eq13960 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11245 eq12575
    | exact resolve eq12575 eq11245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11245 eq12575
  have eq13973 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13960 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13960
  have eq14019 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11596 eq13273
    | exact resolve eq13273 eq11596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11596 eq13273
  have eq14034 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14019 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14019
  have eq14040 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14034 X0
       grind)
    | (have r₁ := eq14034 X0
       have r₂ := eq11740
       grind)
    | exact resolve eq14034 eq11740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11740 eq14034
  have eq14078 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13560 eq13973
    | exact resolve eq13973 eq13560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13973
  have eq14097 : ∀ X0 : G, y = (M.op X0 y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq14078 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14078
  have eq14168 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13560 eq14040
    | exact resolve eq14040 eq13560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13560 eq14040
  have eq14187 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq14168 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14168
  have eq14799 : y = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14097 x
       grind)
    | exact superpose eq14097 eq19
    | (have j1 := eq14097 x
       grind)
    | exact resolve eq19 eq14097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14097
  have eq14805 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq14799
  have eq15591 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19
       have i₂ := eq14187 x
       grind)
    | exact superpose eq14187 eq19
    | (have j1 := eq14187 x
       grind)
    | exact resolve eq19 eq14187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14187
  have eq15597 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15591
  have eq15754 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15597 eq28
    | exact resolve eq28 eq15597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15597
  have eq15778 : y = (M.op x y) := by
    first
    | (have r₁ := eq15754
       have r₂ := eq14805
       grind)
    | exact resolve eq15754 eq14805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14805 eq15754
  have eq15779 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq15778 eq21
    | exact resolve eq21 eq15778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15825 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq15778 eq216
    | exact resolve eq216 eq15778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq15839 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq15778 eq8467
    | exact resolve eq8467 eq15778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8467
  have eq15843 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq15839
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15839
    | exact resolve eq15839 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15839
  have eq15857 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq15825 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15825
    | (have j0 := eq15825 X0
       grind)
    | exact resolve eq15825 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq15825
  have eq15902 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15779
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15779
    | exact resolve eq15779 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15779
  have eq15904 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq15843
    | exact resolve eq15843 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq15843
  have eq15910 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq15778 eq15857
    | exact resolve eq15857 eq15778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15857
  have eq15911 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq15778 eq15904
    | exact resolve eq15904 eq15778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15778 eq15904
  have eq15917 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq15902 eq27
    | exact resolve eq27 eq15902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15902
  have eq16564 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq15911 eq15917
    | exact resolve eq15917 eq15911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15917
  have eq16565 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16564
       have i₂ := eq15910 sF2
       grind)
    | exact superpose eq15910 eq16564
    | exact resolve eq16564 eq15910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15910 eq16564
  have eq16573 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq16565 eq28
    | exact resolve eq28 eq16565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16565
  have eq16603 : False := by grind
  exact eq16603

/-- `Equation432`: `x = x ◇ (y ◇ (x ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_x_pxy_pyx_pxy_Equation432 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law432 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law432.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X0
       have i₂ := eq9 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq30 (σ X0)
       grind)
    | exact superpose eq30 eq15
    | exact resolve eq15 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq32
    | exact resolve eq32 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32
  have eq67 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) (σ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq20
    | exact resolve eq20 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq73
    | (have j0 := eq73 X0 X1
       grind)
    | exact resolve eq73 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq159 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq77
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq176 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq159 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq159
    | (have j0 := eq159 X0 X1
       grind)
    | exact resolve eq159 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159
  have eq184 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq176 X0 X1
       have j1 := eq69 X1 X0
       grind)
    | (have r₁ := eq176 X1 X0
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq176 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq525 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq184
    | exact resolve eq184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq184 (σ X1) X0
       grind)
    | exact superpose eq184 eq15
    | (have j1 := eq184 (σ X1) X0
       grind)
    | exact resolve eq15 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq559 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq525 X0 (τ X1)
       grind)
    | exact superpose eq525 eq18
    | (have j1 := eq525 X0 (τ X1)
       grind)
    | exact resolve eq18 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1429 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq559
    | exact resolve eq559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq1501 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1429 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1429
    | (have j0 := eq1429 X0 X1
       grind)
    | exact resolve eq1429 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429
  have eq2440 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq532 x y
       grind)
    | exact superpose eq532 eq16
    | (have j1 := eq532 x y
       grind)
    | exact resolve eq16 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq2643 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2440
       have i₂ := eq1501 y x
       grind)
    | exact superpose eq1501 eq2440
    | (have j1 := eq1501 (σ y) (σ x)
       grind)
    | (have r₁ := eq2440
       have r₂ := eq1501 y x
       grind)
    | exact resolve eq2440 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501 eq2440
  have eq2644 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq2643
  have eq2651 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 x y
       have i₂ := eq2644
       grind)
    | exact superpose eq2644 eq20
    | exact resolve eq20 eq2644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2644
  have eq2717 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 (σ x) (σ y)
       have i₂ := eq2651
       grind)
    | exact superpose eq2651 eq20
    | exact resolve eq20 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2651
  have eq2727 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2717
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq2717
    | exact resolve eq2717 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2717
  have eq2745 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq67 x
       have i₂ := eq2727
       grind)
    | exact superpose eq2727 eq67
    | exact resolve eq67 eq2727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq2727
  have eq2781 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2745
       have i₂ := eq35 x
       grind)
    | exact superpose eq35 eq2745
    | exact resolve eq2745 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq2745
  have eq2782 : (σ x) = (σ (M.op x x)) := by grind
  clear eq2781
  have eq2868 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq69 x X0
       have i₂ := eq2782
       grind)
    | exact superpose eq2782 eq69
    | (have j0 := eq69 x X0
       grind)
    | exact resolve eq69 eq2782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq2872 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2782
       grind)
    | exact superpose eq2782 eq10
    | exact resolve eq10 eq2782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2782
  have eq2932 : x = (M.op x x) := by
    first
    | (have i₁ := eq2872
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2872
    | exact resolve eq2872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq2936 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq2868 X0
       have j1 := eq525 (σ x) X0
       grind)
    | (have r₁ := eq2868 x
       have r₂ := eq525 (σ x) x
       grind)
    | exact resolve eq2868 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868
  have eq2946 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 x X0
       have i₂ := eq2932
       grind)
    | exact superpose eq2932 eq12
    | (have j0 := eq12 x X0
       grind)
    | exact resolve eq12 eq2932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2932
  have eq2993 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq2946 X0
       have j1 := eq525 x X0
       grind)
    | (have r₁ := eq2946 x
       have r₂ := eq525 x x
       grind)
    | exact resolve eq2946 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq2946
  have eq3290 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k x X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq2936 (σ X0)
       grind)
    | exact superpose eq2936 eq15
    | exact resolve eq15 eq2936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2936
  have eq3336 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq3290 X0
       have i₂ := eq2993 X0
       grind)
    | exact superpose eq2993 eq3290
    | exact resolve eq3290 eq2993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2993 eq3290
  have eq3942 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3336 y
       grind)
    | exact superpose eq3336 eq16
    | (have r₁ := eq16
       have r₂ := eq3336 y
       grind)
    | exact resolve eq16 eq3336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq3988 : False := by grind
  exact eq3988

/-- `Equation432`: `x = x ◇ (y ◇ (x ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation432 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law432 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law432.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) X0 X0
       have i₂ := eq14 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq73
    | exact resolve eq73 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq80
    | exact resolve eq80 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82
    | exact resolve eq82 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq92 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq100 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq154 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq213 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq221 : (M.op x y) ≠ (M.op x y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq213 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq213
       grind)
    | exact resolve eq13 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq222 : y = (k y (M.op x y)) := by grind
  clear eq221
  have eq225 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq222 eq92
    | exact resolve eq92 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq229 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq225
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq225
    | exact resolve eq225 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq232 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq229 eq11
    | (have j0 := eq11 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq232
  have eq236 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq244 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq236 eq13
    | (have j0 := eq13 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq236
       grind)
    | exact resolve eq13 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq245 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq244
  have eq259 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X1
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq12
    | (have j0 := eq12 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq12 (M.op X1 X0) X0
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq12 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq13 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq266 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k (M.op X0 X1) X1) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq648 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq650 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq649 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq886 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq233 eq12
    | (have j0 := eq12 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq12 (σ y) (σ (M.op x y))
       have r₂ := eq233
       grind)
    | (have r₁ := eq12 (σ (M.op x y)) (σ y)
       have r₂ := eq233
       grind)
    | exact resolve eq12 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq894 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq886
  have eq895 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq894
  have eq896 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq229 eq895
    | exact resolve eq895 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq895
  have eq929 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq896 eq59
    | exact resolve eq59 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq3595 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq650 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq650
    | (have j0 := eq650 (τ X0)
       grind)
    | exact resolve eq650 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq650
  have eq3604 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3595 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3595
    | (have j0 := eq3595 X0
       grind)
    | exact resolve eq3595 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3595
  have eq3610 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3604 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3604
    | (have j0 := eq3604 X0
       grind)
    | exact resolve eq3604 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3604
  have eq11813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq83 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq11814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq11813
    | exact resolve eq11813 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11813
  have eq11825 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq11814
       have r₂ := eq27
       grind)
    | exact resolve eq11814 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11814
  have eq11828 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq11825
    | exact resolve eq11825 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11825
  have eq12575 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq11828 eq265
    | exact resolve eq265 eq11828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq11828
  have eq12598 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq12575 eq55
    | exact resolve eq55 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq12575
  have eq12627 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq12598
    | exact resolve eq12598 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12598
  have eq12630 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq12627
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq12627
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq12627
       have r₂ := eq13 x y
       grind)
    | exact resolve eq12627 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12627
  have eq12729 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq12630
       grind)
    | exact superpose eq12630 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq12630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12733 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq648 x y
       have i₂ := eq12630
       grind)
    | exact superpose eq12630 eq648
    | (have j0 := eq648 x y
       grind)
    | exact resolve eq648 eq12630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12630
  have eq12738 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12733
  have eq12740 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12729
  have eq12744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12738
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12738
    | exact resolve eq12738 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12738
  have eq12748 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12740
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12740
    | exact resolve eq12740 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12740
  have eq12749 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12748
  have eq12761 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12744
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12744
    | exact resolve eq12744 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12744
  have eq12767 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12761
    | exact resolve eq12761 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12761
  have eq12768 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12767
  have eq12775 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12768
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12768
    | exact resolve eq12768 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12768
  have eq12780 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12775
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12775
    | exact resolve eq12775 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12775
  have eq12798 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq266 y x
       have i₂ := eq12749
       grind)
    | exact superpose eq12749 eq266
    | exact resolve eq266 eq12749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12749
  have eq12807 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12798
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12798
    | exact resolve eq12798 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12798
  have eq12814 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12807
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12807
    | exact resolve eq12807 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12807
  have eq12815 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12814
  have eq12866 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12780 eq266
    | exact resolve eq266 eq12780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12780
  have eq12875 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12866
    | exact resolve eq12866 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12866
  have eq12882 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12875
    | exact resolve eq12875 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12875
  have eq12883 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12882
  have eq13024 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq12815
       grind)
    | exact superpose eq12815 eq90
    | exact resolve eq90 eq12815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq12815
  have eq13050 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq13024
    | exact resolve eq13024 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13024
  have eq13976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13050 eq12883
    | exact resolve eq12883 eq13050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12883 eq13050
  have eq13985 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13976
  have eq13987 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq13985
       have r₂ := eq27
       grind)
    | exact resolve eq13985 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13985
  have eq14005 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13987 eq245
    | exact resolve eq245 eq13987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq13987
  have eq14107 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14005 eq100
    | exact resolve eq100 eq14005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq14005
  have eq14141 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq14107
    | exact resolve eq14107 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14107
  have eq14144 : y = (k y x) := by
    first
    | (have r₁ := eq14141
       have r₂ := eq50
       grind)
    | exact resolve eq14141 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq14141
  have eq14170 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq14144
       grind)
    | exact superpose eq14144 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq14144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14174 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq648 y x
       have i₂ := eq14144
       grind)
    | exact superpose eq14144 eq648
    | (have j0 := eq648 y x
       grind)
    | exact resolve eq648 eq14144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq14180 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq14174
  have eq14182 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq14170
  have eq14187 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14180
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14180
    | exact resolve eq14180 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14180
  have eq14191 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14182
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14182
    | exact resolve eq14182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14182
  have eq14203 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14187
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14187
    | exact resolve eq14187 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14187
  have eq14211 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq14203
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14203
    | exact resolve eq14203 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14203
  have eq14218 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq14211
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14211
    | exact resolve eq14211 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14211
  have eq14225 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14218
    | exact resolve eq14218 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14218
  have eq15286 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq14191
       grind)
    | exact superpose eq14191 eq14
    | exact resolve eq14 eq14191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15292 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq266 y x
       have i₂ := eq14191
       grind)
    | exact superpose eq14191 eq266
    | exact resolve eq266 eq14191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266 eq14191
  have eq15305 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15292
       have i₂ := eq14144
       grind)
    | exact superpose eq14144 eq15292
    | exact resolve eq15292 eq14144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14144 eq15292
  have eq15309 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq15286 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15286
    | (have j0 := eq15286 X0
       grind)
    | exact resolve eq15286 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15286
  have eq15312 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15305
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15305
    | exact resolve eq15305 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15305
  have eq15315 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15312
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15312
    | exact resolve eq15312 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15312
  have eq15316 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15315
  have eq15318 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15316 eq20
    | exact resolve eq20 eq15316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15380 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq15424 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15318
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15318
    | exact resolve eq15318 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15318
  have eq15534 : (k y (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15424 eq118
    | exact resolve eq118 eq15424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq15424
  have eq15656 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq154 eq15534
    | exact resolve eq15534 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq15534
  have eq15671 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq222 eq15656
    | exact resolve eq15656 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq15656
  have eq17081 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15671 eq3610
    | (have j0 := eq3610 (M.op x y)
       grind)
    | exact resolve eq3610 eq15671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3610 eq15671
  have eq17108 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17081
       have r₂ := eq15316
       grind)
    | exact resolve eq17081 eq15316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17081
  have eq18503 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17108 eq15309
    | exact resolve eq15309 eq17108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15309 eq17108
  have eq18539 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq18503
  have eq18549 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq15316 eq18539
    | exact resolve eq18539 eq15316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15316 eq18539
  have eq18571 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18549
       have r₂ := eq15380
       grind)
    | exact resolve eq18549 eq15380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15380 eq18549
  have eq18572 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18571
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18571
    | exact resolve eq18571 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18571
  have eq18573 : x = (M.op x y) := by grind
  clear eq18572
  have eq18575 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18573 eq20
    | exact resolve eq20 eq18573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq18573
  have eq18684 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18575
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18575
    | exact resolve eq18575 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18575
  have eq18691 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18684 eq26
    | exact resolve eq26 eq18684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq18761 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18684 eq14225
    | exact resolve eq14225 eq18684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14225 eq18684
  have eq18769 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq18761
       have r₂ := eq27
       grind)
    | exact resolve eq18761 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18761
  have eq18846 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18691 eq896
    | exact resolve eq896 eq18691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq18864 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq18846
       have r₂ := eq27
       grind)
    | exact resolve eq18846 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18846
  have eq18898 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ (M.op x y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq18769 eq14
    | exact resolve eq14 eq18769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18769
  have eq18927 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq18691 eq18898
    | exact resolve eq18898 eq18691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18898
  have eq18941 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq18864 eq18927
    | exact resolve eq18927 eq18864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18864 eq18927
  have eq19750 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq929 eq18941
    | exact resolve eq18941 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq18941
  have eq19783 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq19750
  have eq19790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18691 eq19783
    | exact resolve eq19783 eq18691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18691 eq19783
  have eq19803 : False := by grind
  exact eq19803

/-- `Equation432`: `x = x ◇ (y ◇ (x ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_pxx_pyx_Equation432 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law432 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law432.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X0)))) = X0 := by
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
  have eq51 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op y (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
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
  have eq75 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq93
    | exact resolve eq93 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq109 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq212 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq3244 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq10856 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10856
    | exact resolve eq10856 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10856
  have eq10868 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq10857
       have r₂ := eq28
       grind)
    | exact resolve eq10857 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10857
  have eq10870 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10868
    | exact resolve eq10868 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10868
  have eq10872 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq10870
  have eq10886 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq10872
    | exact resolve eq10872 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10872
  have eq11003 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq10886 eq95
    | exact resolve eq95 eq10886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10886
  have eq11016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11003
  have eq11018 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11016
       have r₂ := eq28
       grind)
    | exact resolve eq11016 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11016
  have eq11025 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11018
  have eq11041 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11025
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11025
    | exact resolve eq11025 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11025
  have eq11067 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq11041
       grind)
    | exact superpose eq11041 eq70
    | exact resolve eq70 eq11041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11041
  have eq11091 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11067
    | exact resolve eq11067 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11067
  have eq11142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11091 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11145 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11142
    | exact resolve eq11142 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11142
  have eq11156 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11145
       have r₂ := eq28
       grind)
    | exact resolve eq11145 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11145
  have eq11158 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11156
    | exact resolve eq11156 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11156
  have eq11159 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11158
  have eq11162 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11159
  have eq11178 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11162
    | exact resolve eq11162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11162
  have eq12079 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11178 eq11091
    | exact resolve eq11091 eq11178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11091 eq11178
  have eq12087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12079
  have eq12091 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12087
       have r₂ := eq28
       grind)
    | exact resolve eq12087 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12087
  have eq12208 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12091 eq110
    | (have r₁ := eq110
       have r₂ := eq12091
       grind)
    | exact resolve eq110 eq12091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq12209 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12091 eq212
    | exact resolve eq212 eq12091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq12091
  have eq12217 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12208
  have eq34816 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12217 eq92
    | exact resolve eq92 eq12217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq12217
  have eq133367 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12209 eq34816
    | exact resolve eq34816 eq12209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12209 eq34816
  have eq133621 : (τ (σ y)) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq133367
  have eq133630 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq133621
    | exact resolve eq133621 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq133621
  have eq134491 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq133630
  have eq134513 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq134491
    | exact resolve eq134491 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134491
  have eq134554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134513 eq95
    | exact resolve eq95 eq134513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq134577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by grind
  clear eq134554
  have eq134581 : y = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq134577
       have r₂ := eq28
       grind)
    | exact resolve eq134577 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134577
  have eq135441 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq134581
       grind)
    | exact superpose eq134581 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq134581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134581
  have eq135450 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq135441
  have eq135460 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq135450
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq135450
    | exact resolve eq135450 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135450
  have eq135461 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq135460
  have eq135488 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq135461
  have eq135510 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq135488
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq135488
    | exact resolve eq135488 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135488
  have eq135550 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq135510
       grind)
    | exact superpose eq135510 eq70
    | exact resolve eq70 eq135510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135591 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq135550
    | exact resolve eq135550 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135550
  have eq135634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq135591 eq134513
    | exact resolve eq134513 eq135591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134513 eq135591
  have eq135644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ y = (M.op x y) := by grind
  clear eq135634
  have eq135653 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq135644
       have r₂ := eq28
       grind)
    | exact resolve eq135644 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135644
  have eq135687 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq135510
       have i₂ := eq135653
       grind)
    | exact superpose eq135653 eq135510
    | exact resolve eq135510 eq135653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135510 eq135653
  have eq135698 : y = (M.op x y) := by grind
  clear eq135687
  have eq135732 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq135698 eq21
    | exact resolve eq21 eq135698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq135741 : y ≠ y ∨ y = (M.op x x) ∨ (k y x) = (M.op y y) := by
    first
    | exact superpose eq135698 eq109
    | (have r₁ := eq109
       have r₂ := eq135698
       grind)
    | exact resolve eq109 eq135698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq135783 : y = (M.op y y) := by
    first
    | exact superpose eq135698 eq207
    | exact resolve eq207 eq135698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq135874 : y = (M.op x x) ∨ (k y x) = (M.op y y) := by grind
  clear eq135741
  have eq136002 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq135732
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq135732
    | exact resolve eq135732 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135732
  have eq137076 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq136002 eq27
    | exact resolve eq27 eq136002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq148173 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq136002 eq3244
    | (have j0 := eq3244 X0
       grind)
    | exact resolve eq3244 eq136002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3244
  have eq148174 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq136002 eq148173
    | (have j0 := eq148173 X0
       grind)
    | exact resolve eq148173 eq136002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148173
  have eq148175 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq136002 eq148174
    | (have j0 := eq148174 X0
       grind)
    | exact resolve eq148174 eq136002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148174
  have eq153064 : y = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq135874
       have i₂ := eq135783
       grind)
    | exact superpose eq135783 eq135874
    | exact resolve eq135874 eq135783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135783 eq135874
  have eq153068 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq70
       have i₂ := eq153064
       grind)
    | exact superpose eq153064 eq70
    | exact resolve eq70 eq153064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153084 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq148175 x
       have i₂ := eq153064
       grind)
    | exact superpose eq153064 eq148175
    | (have j0 := eq148175 x
       grind)
    | exact resolve eq148175 eq153064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153064
  have eq153111 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153084
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq153084
    | exact resolve eq153084 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153084
  have eq153125 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq136002 eq153068
    | exact resolve eq153068 eq136002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153068
  have eq153134 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq153111
       have r₂ := eq136002
       grind)
    | exact resolve eq153111 eq136002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153111
  have eq153148 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153125
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq153125
    | exact resolve eq153125 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153125
  have eq153154 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153134
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq153134
    | exact resolve eq153134 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153134
  have eq153168 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq136002 eq153148
    | exact resolve eq153148 eq136002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153148
  have eq153172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq137076 eq153154
    | exact resolve eq153154 eq137076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153154
  have eq153179 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq153172
       have r₂ := eq28
       grind)
    | exact resolve eq153172 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153172
  have eq153183 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq153179
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq153179
    | exact resolve eq153179 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153179
  have eq153278 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq153183
  have eq153303 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq137076 eq153278
    | exact resolve eq153278 eq137076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153278
  have eq153420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq153303 eq153168
    | exact resolve eq153168 eq153303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153168 eq153303
  have eq153433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq153420
  have eq153437 : y = (M.op x x) := by
    first
    | (have r₁ := eq153433
       have r₂ := eq28
       grind)
    | exact resolve eq153433 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153433
  have eq153451 : (M.op x y) = (k y x) := by grind
  clear eq153437
  have eq153474 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq153451
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq153451
    | exact resolve eq153451 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq153451
  have eq153485 : y = (k y x) := by
    first
    | exact superpose eq135698 eq153474
    | exact resolve eq153474 eq135698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135698 eq153474
  have eq153558 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq70
       have i₂ := eq153485
       grind)
    | exact superpose eq153485 eq70
    | exact resolve eq70 eq153485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq153574 : (σ y) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq148175 x
       have i₂ := eq153485
       grind)
    | exact superpose eq153485 eq148175
    | (have j0 := eq148175 x
       grind)
    | exact resolve eq148175 eq153485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148175 eq153485
  have eq153597 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153574
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq153574
    | exact resolve eq153574 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153574
  have eq153610 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq136002 eq153558
    | exact resolve eq153558 eq136002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153558
  have eq153617 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq153597
       have r₂ := eq136002
       grind)
    | exact resolve eq153597 eq136002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153597
  have eq153630 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq153610
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq153610
    | exact resolve eq153610 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq153610
  have eq153635 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153617
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq153617
    | exact resolve eq153617 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153617
  have eq153648 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq136002 eq153630
    | exact resolve eq153630 eq136002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136002 eq153630
  have eq153652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq137076 eq153635
    | exact resolve eq153635 eq137076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153635
  have eq153659 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq153652
       have r₂ := eq28
       grind)
    | exact resolve eq153652 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153652
  have eq153663 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153659
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq153659
    | exact resolve eq153659 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq153659
  have eq153757 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq153663
  have eq153780 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq137076 eq153757
    | exact resolve eq153757 eq137076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137076 eq153757
  have eq153785 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153648 eq153780
    | exact resolve eq153780 eq153648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153648 eq153780
  have eq153789 : False := by grind
  exact eq153789
