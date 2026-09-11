import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq92 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq92
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq77097 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq14
    | exact resolve eq14 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq77252 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq77097 x
       have i₂ := eq14 x y x
       grind)
    | exact superpose eq14 eq77097
    | exact resolve eq77097 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77097
  have eq77253 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq77252
  have eq77392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq77253 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq77253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77253
  have eq77404 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq77392
    | exact resolve eq77392 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77392
  have eq77417 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq77404
       have r₂ := eq28
       grind)
    | exact resolve eq77404 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77404
  have eq77456 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op (σ y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq77417 eq14
    | exact resolve eq14 eq77417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77417
  have eq77611 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq77456 x
       have i₂ := eq14 sF2 sF3 x
       grind)
    | exact superpose eq14 eq77456
    | exact resolve eq77456 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77456
  have eq77612 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq77611
  have eq77721 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq77612 eq30
    | exact resolve eq30 eq77612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq77612
  have eq77877 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq77721
    | exact resolve eq77721 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq77721
  have eq77878 : x = y := by grind
  clear eq77877
  have eq78202 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq77878
       grind)
    | exact superpose eq77878 eq19
    | exact resolve eq19 eq77878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq78203 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq77878
       grind)
    | exact superpose eq77878 eq25
    | exact resolve eq25 eq77878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq77878
  have eq78355 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq78203
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq78203
    | exact resolve eq78203 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq78203
  have eq78374 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq78355 eq27
    | exact resolve eq27 eq78355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq78355
  have eq79451 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq78374 eq70
    | exact resolve eq70 eq78374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq78374
  have eq79615 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq79451
       have i₂ := eq78202
       grind)
    | exact superpose eq78202 eq79451
    | exact resolve eq79451 eq78202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78202 eq79451
  have eq79656 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq79615 eq15
    | exact resolve eq15 eq79615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79615
  have eq79737 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq79656
    | exact resolve eq79656 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq79656
  have eq79758 : False := by grind
  exact eq79758

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pyx_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq103 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) X3))) = (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq103 (M.op (M.op X5 (M.op X1 X2)) X3) X2 X1 X4
       have i₂ := eq103 X3 (M.op X1 X2) X5 X0
       grind)
    | exact superpose eq103 eq103
    | exact resolve eq103 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq103 X2 X0 X1 x
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 x
       have i₂ := eq103 (M.op X1 X2) X1 x X0
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq310 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq303 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq303
    | (have j0 := eq303 X0 X1
       grind)
    | exact resolve eq303 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq316 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq310 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq310
    | (have j0 := eq310 X0 X1
       grind)
    | exact resolve eq310 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq330 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq268 X1 X2 (M.op (M.op X3 (M.op X2 X1)) (M.op (M.op X2 X1) X0))
       have i₂ := eq9 X0 (M.op X2 X1) X3
       grind)
    | exact superpose eq9 eq268
    | exact resolve eq268 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq268 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X2 X1)) X0))
       have i₂ := eq268 (M.op X2 X1) X3 X0
       grind)
    | exact superpose eq268 eq268
    | exact resolve eq268 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X1 X2) X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq268 X2 X1 (M.op (M.op X4 (M.op X1 X2)) X3)
       have i₂ := eq103 X3 (M.op X1 X2) X4 X0
       grind)
    | exact superpose eq103 eq268
    | exact resolve eq268 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) X0) = (M.op X2 (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X3 X2) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq103 (M.op X2 (M.op (M.op X3 X2) X0)) X2 X4 X1
       have i₂ := eq268 X2 X3 X0
       grind)
    | exact superpose eq268 eq103
    | exact resolve eq103 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq335 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X3 X2) X0) X2 x
       grind)
    | exact superpose eq9 eq335
    | exact resolve eq335 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq354 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 (M.op X2 (M.op X2 X3)))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq332 x X1 X2 X3 X4
       have i₂ := eq330 X3 X2 X1 x
       grind)
    | exact superpose eq330 eq332
    | exact resolve eq332 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq357 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X2) (M.op X2 (M.op (M.op X5 (M.op X1 X2)) X3))) = (M.op X2 (M.op X2 (M.op X2 X3))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq265 x X1 X2 X3 X4 X5
       have i₂ := eq330 X3 X2 X1 x
       grind)
    | exact superpose eq330 eq265
    | exact resolve eq265 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq330
  have eq422 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X4 (M.op X2 (M.op X2 X0))) X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq103 X3 (M.op X2 (M.op X2 X0)) X4 (M.op x X2)
       have i₂ := eq281 x X2 X0
       grind)
    | exact superpose eq281 eq103
    | exact resolve eq103 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq424 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) (M.op (M.op X2 X0) X3)) = (M.op X0 (M.op (M.op X2 (M.op X2 X0)) X3)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq422 X0 X2 X3 x
       have i₂ := eq331 X3 (M.op X2 X0) X2 x
       grind)
    | exact superpose eq331 eq422
    | exact resolve eq422 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq422
  have eq1410 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq316 x y
       grind)
    | exact superpose eq316 eq16
    | (have j1 := eq316 x y
       grind)
    | exact resolve eq16 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq8452 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq344 (M.op (M.op X2 X3) (M.op (M.op X2 X3) (M.op (M.op X2 X3) X4))) X5 X3 X2
       have i₂ := eq354 X1 (M.op X2 X3) X4 X0
       grind)
    | exact superpose eq354 eq344
    | exact resolve eq344 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344 eq354
  have eq8480 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op (M.op X5 X3) (M.op X3 (M.op (M.op X2 (M.op X2 X3)) (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq8452 X0 X1 X2 X3 X4 X5
       have i₂ := eq424 X3 X2 (M.op (M.op X2 X3) X4)
       grind)
    | exact superpose eq424 eq8452
    | exact resolve eq8452 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq8452
  have eq8735 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) = (M.op X3 (M.op X3 (M.op X3 (M.op (M.op X2 X3) X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8480 X0 X1 X2 X3 X4 x
       have i₂ := eq357 X2 X3 (M.op (M.op X2 X3) X4) x X2
       grind)
    | exact superpose eq357 eq8480
    | exact resolve eq8480 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq8480
  have eq8889 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq8735 X0 X1 X2 X3 X4
       have i₂ := eq268 X3 X2 X4
       grind)
    | exact superpose eq268 eq8735
    | exact resolve eq8735 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq8735
  have eq193745 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1410
       grind)
    | exact superpose eq1410 eq10
    | exact resolve eq10 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq193886 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq193745
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq193745
    | exact resolve eq193745 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193745
  have eq1854144 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq193886
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq193886
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq193886
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq193886
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq193886 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193886
  have eq1854145 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1854144
  have eq1854146 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1854145
  have eq1854483 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op X1 (M.op X2 (M.op x x))) X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8889 X1 X2 y y X0
       have i₂ := eq1854146
       grind)
    | exact superpose eq1854146 eq8889
    | exact resolve eq8889 eq1854146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1854841 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1854483 X0 x x
       have i₂ := eq8889 x x x x X0
       grind)
    | exact superpose eq8889 eq1854483
    | exact resolve eq1854483 eq8889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8889 eq1854483
  have eq1855027 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1854146
       have i₂ := eq1854841 y
       grind)
    | exact superpose eq1854841 eq1854146
    | exact resolve eq1854146 eq1854841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1854146 eq1854841
  have eq1856275 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1855027
  have eq1857110 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x x))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq281 X0 x y
       have i₂ := eq1856275
       grind)
    | exact superpose eq1856275 eq281
    | exact resolve eq281 eq1856275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856275
  have eq1857553 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1857110 x
       have i₂ := eq281 x x x
       grind)
    | exact superpose eq281 eq1857110
    | exact resolve eq1857110 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq1857110
  have eq1857554 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1857553
  have eq1857582 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1857554
       grind)
    | exact superpose eq1857554 eq10
    | exact resolve eq10 eq1857554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857554
  have eq1857824 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1857582
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1857582
    | exact resolve eq1857582 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857582
  have eq1857825 : x = y := by grind
  clear eq1857824
  have eq1857837 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1857825
       grind)
    | exact superpose eq1857825 eq16
    | exact resolve eq16 eq1857825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857825
  have eq1858322 : False := by grind
  exact eq1858322

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxy_pxx_pyx_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq29 : x = (τ (σ x)) := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq723 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq723
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq723
    | exact resolve eq723 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq836 : (M.op x y) = (k y x) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq715
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq715
    | exact resolve eq715 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq1056 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq836
       grind)
    | exact superpose eq836 eq39
    | exact resolve eq39 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq1057 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1056
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1056
    | exact resolve eq1056 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1059 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq1057
    | exact resolve eq1057 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1764 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1059 eq828
    | exact resolve eq828 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq1059
  have eq1771 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq1764
       have r₂ := eq27
       grind)
    | exact resolve eq1764 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq1781 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1771 eq181
    | exact resolve eq181 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771
  have eq1782 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq179 eq1781
    | exact resolve eq1781 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1781
  have eq1783 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1782
  have eq1792 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq181 x X0
       have i₂ := eq1783
       grind)
    | exact superpose eq1783 eq181
    | exact resolve eq181 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq1783
  have eq1793 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq178 eq1792
    | exact resolve eq1792 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1792
  have eq1794 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1793
  have eq1799 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1794 eq31
    | exact resolve eq31 eq1794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1794
  have eq1838 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1799
    | exact resolve eq1799 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1799
  have eq1839 : x = y := by grind
  clear eq1838
  have eq1842 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1839
       grind)
    | exact superpose eq1839 eq18
    | exact resolve eq18 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1843 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1839
       grind)
    | exact superpose eq1839 eq24
    | exact resolve eq24 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1839
  have eq1865 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1843
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1843
    | exact resolve eq1843 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq1866 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1842
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1842
    | exact resolve eq1842 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq1869 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1865 eq26
    | exact resolve eq26 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1865
  have eq1909 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1869
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1869
    | exact resolve eq1869 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq1869
  have eq1914 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1866
       grind)
    | exact superpose eq1866 eq39
    | exact resolve eq39 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1866
  have eq1920 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1914
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1914
    | exact resolve eq1914 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1914
  have eq1924 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1909 eq1920
    | exact resolve eq1920 eq1909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909 eq1920
  have eq1928 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1924
    | exact resolve eq1924 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1924
  have eq1930 : False := by grind
  exact eq1930

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_pyy_pyx_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq56 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : x ≠ (M.op x y) ∨ x = y ∨ (M.op x x) = (k y x) := by
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
  have eq83 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq665 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (M.op X2 X0) X2 x X1
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq668 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq57 eq58
    | exact resolve eq58 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq58
  have eq1148 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq104 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq1149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1148
    | exact resolve eq1148 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1152 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1149
       have r₂ := eq28
       grind)
    | exact resolve eq1149 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149
  have eq1154 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1152
    | exact resolve eq1152 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1159 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1154 eq83
    | (have r₁ := eq83
       have r₂ := eq1154
       grind)
    | exact resolve eq83 eq1154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1154
  have eq1163 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1159
  have eq1164 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1163
  have eq1169 : (τ (M.op (σ x) (σ x))) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1164 eq101
    | exact resolve eq101 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq1164
  have eq1176 : (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq70 eq1169
    | exact resolve eq1169 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1179 : (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1176
       have r₂ := eq82
       grind)
    | exact resolve eq1176 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq1176
  have eq1182 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq89
       have i₂ := eq1179
       grind)
    | exact superpose eq1179 eq89
    | exact resolve eq89 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1183 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq1179
       grind)
    | exact superpose eq1179 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1184 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1183
  have eq1186 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1184
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1184
    | exact resolve eq1184 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1187 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1182
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq1182
    | exact resolve eq1182 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1182
  have eq1189 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1186
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1186
    | exact resolve eq1186 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1196 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1187 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1197 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1196
  have eq1201 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1197
    | exact resolve eq1197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1204 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1201
    | exact resolve eq1201 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1230 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq665 x X0 x
       have i₂ := eq1189
       grind)
    | exact superpose eq1189 eq665
    | exact resolve eq665 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1232 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq667 eq1230
    | exact resolve eq1230 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq1230
  have eq1233 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1232
  have eq1238 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1233 eq30
    | exact resolve eq30 eq1233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1233
  have eq1260 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1238
    | exact resolve eq1238 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1261 : x = (M.op x y) ∨ x = y := by grind
  clear eq1260
  have eq1265 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1261 eq21
    | exact resolve eq21 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1290 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1265
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1265
    | exact resolve eq1265 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq20710 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1204 eq665
    | exact resolve eq665 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665 eq1204
  have eq20735 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq668 eq20710
    | exact resolve eq20710 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq20710
  have eq20736 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq20735
  have eq20740 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20736 eq28
    | exact resolve eq28 eq20736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20736
  have eq20769 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20740
       have r₂ := eq1290
       grind)
    | exact resolve eq20740 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290 eq20740
  have eq20981 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq20769 eq30
    | exact resolve eq30 eq20769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20769
  have eq21039 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq20981
    | exact resolve eq20981 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20981
  have eq21040 : x = y := by grind
  clear eq21039
  have eq21043 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq21040
       grind)
    | exact superpose eq21040 eq19
    | exact resolve eq19 eq21040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21044 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq21040
       grind)
    | exact superpose eq21040 eq25
    | exact resolve eq25 eq21040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq21040
  have eq21082 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq21044
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq21044
    | exact resolve eq21044 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq21044
  have eq21085 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21082 eq27
    | exact resolve eq27 eq21082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21082
  have eq21226 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq21085 eq70
    | exact resolve eq70 eq21085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq21085
  have eq21296 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq21226
       have i₂ := eq21043
       grind)
    | exact superpose eq21043 eq21226
    | exact resolve eq21226 eq21043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21043 eq21226
  have eq21299 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21296 eq15
    | exact resolve eq15 eq21296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21296
  have eq21345 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq21299
    | exact resolve eq21299 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq21299
  have eq21354 : False := by grind
  exact eq21354

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pxy_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq58 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq10
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op X2 (M.op (M.op X3 X2) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X2) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq91 X0 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq91
    | exact resolve eq91 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1))
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq91
    | exact resolve eq91 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq105
    | exact resolve eq105 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq115 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq121 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq115 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq115
    | (have j0 := eq115 X0 X1
       grind)
    | exact resolve eq115 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq134 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq110
    | exact resolve eq110 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq134 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq134
    | exact resolve eq134 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq194 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (σ X0)) X1) = (M.op (σ X0) (M.op (M.op X3 (σ X0)) (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq96 X2 (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) (σ X0) X3
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq96
    | exact resolve eq96 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq216 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 (M.op (M.op X3 X0) X2))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq96 x X2 X0 X3
       grind)
    | exact superpose eq96 eq9
    | exact resolve eq9 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op (M.op X1 X0) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0
       have i₂ := eq96 X0 X0 X0 X1
       grind)
    | exact superpose eq96 eq110
    | exact resolve eq110 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 x
       have i₂ := eq96 X1 (M.op X0 X2) X0 x
       grind)
    | exact superpose eq96 eq9
    | exact resolve eq9 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (σ X0)) X1) = (M.op (σ X0) (M.op (M.op X3 (σ X0)) (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq194 X0 X1 X2 X3
       have i₂ := eq106 X0 X1
       grind)
    | exact superpose eq106 eq194
    | exact resolve eq194 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq194
  have eq240 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op X2 (σ X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq236 X0 X1 X2 x
       have i₂ := eq9 (M.op (σ (M.op X0 X0)) X1) (σ X0) x
       grind)
    | exact superpose eq9 eq236
    | exact resolve eq236 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq255 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq216 X2 (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X1 X2)) X0)) X1
       have i₂ := eq216 (M.op X1 X2) X0 X3
       grind)
    | exact superpose eq216 eq216
    | exact resolve eq216 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X4 X1) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq96 X3 (M.op X1 (M.op (M.op X2 X1) X0)) X1 X4
       have i₂ := eq216 X1 X0 X2
       grind)
    | exact superpose eq216 eq96
    | exact resolve eq96 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X3 X1) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq259 X0 X1 X2 X3 x
       have i₂ := eq9 (M.op (M.op X2 X1) X0) X1 x
       grind)
    | exact superpose eq9 eq259
    | exact resolve eq259 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq392 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (M.op (M.op X0 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X1
       have i₂ := eq266 (M.op X1 X1) X1 X1 X0
       grind)
    | (have i₁ := eq110 X1
       have i₂ := eq266 (M.op X1 X1) X1 X0 X1
       grind)
    | exact superpose eq266 eq110
    | exact resolve eq110 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq397 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 (M.op X3 X2)) (M.op (M.op X0 X2) X1)) = (M.op (M.op X3 X2) (M.op (M.op X5 (M.op X3 X2)) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq96 X4 X1 (M.op X3 X2) X5
       have i₂ := eq266 X1 X2 X3 X0
       grind)
    | (have i₁ := eq96 X4 X1 (M.op X3 X2) X5
       have i₂ := eq266 X1 X2 X0 X3
       grind)
    | exact superpose eq266 eq96
    | exact resolve eq96 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq418 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X2 X1)) = (M.op (M.op X4 (M.op X3 X2)) (M.op (M.op X0 X2) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq397 X0 X1 X2 X3 X4 x
       have i₂ := eq255 X1 X3 X2 x
       grind)
    | exact superpose eq255 eq397
    | exact resolve eq397 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq397
  have eq824 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X3) = (M.op (M.op X2 (σ (M.op X0 (M.op (M.op X1 X0) X0)))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq266 X3 (σ (M.op X0 (M.op (M.op X1 X0) X0))) X2 (σ X0)
       have i₂ := eq218 X0 X1
       grind)
    | exact superpose eq218 eq266
    | exact resolve eq266 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq941 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (σ (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq392 X1 (τ X0)
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq392
    | exact resolve eq392 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq971 : ∀ X0 X1 : G, (M.op X0 (σ (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq941 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq941
    | exact resolve eq941 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq941
  have eq1051 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X0 X1))) = (σ (M.op (M.op X2 (τ (M.op X0 X1))) (τ (M.op (M.op X0 X1) (M.op X0 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq216 X1 (σ (M.op (M.op X2 (τ (M.op X0 X1))) (τ (M.op (M.op X0 X1) (M.op X0 X1))))) X0
       have i₂ := eq971 (M.op X0 X1) X2
       grind)
    | exact superpose eq971 eq216
    | exact resolve eq216 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq8588 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op (σ (σ X0)) (σ (σ (M.op (M.op X1 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0
       have i₂ := eq266 (M.op X0 X0) X0 X0 X1
       grind)
    | (have i₁ := eq142 X0
       have i₂ := eq266 (M.op X0 X0) X0 X1 X0
       grind)
    | exact superpose eq266 eq142
    | exact resolve eq142 eq266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq266
  have eq14970 : ∀ X1 X2 X3 X4 : G, (M.op (σ (M.op (M.op X1 X2) X2)) X3) = (M.op (M.op X4 (σ (M.op (M.op (M.op X1 X2) X2) (M.op X2 (M.op X2 X2))))) X3) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq824 (M.op (M.op X1 X2) X2) x X4 X3
       have i₂ := eq418 X1 X2 X2 (M.op X1 X2) x
       grind)
    | exact superpose eq418 eq824
    | exact resolve eq824 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq824
  have eq15194 : ∀ X1 X2 X3 X4 : G, (M.op (σ (M.op (M.op X1 X2) X2)) X3) = (M.op (M.op X4 (σ X2)) X3) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq14970 X1 X2 X3 X4
       have i₂ := eq227 X2 (M.op X1 X2) X2
       grind)
    | exact superpose eq227 eq14970
    | exact resolve eq14970 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq14970
  have eq15568 : ∀ X0 X2 X3 : G, (M.op (σ (M.op X0 X0)) X3) = (M.op (σ (M.op (M.op X2 X0) X0)) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq240 X0 X3 x
       have i₂ := eq15194 X2 X0 X3 x
       grind)
    | exact superpose eq15194 eq240
    | exact resolve eq240 eq15194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq15194
  have eq18516 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq130 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq130 X0 X1
       grind)
    | exact superpose eq130 eq10
    | (have j1 := eq130 X0 X1
       grind)
    | exact resolve eq10 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq18568 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18516 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18516
    | (have j0 := eq18516 X0 X1
       grind)
    | exact resolve eq18516 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18516
  have eq25151 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (σ (M.op (M.op X1 (τ X0)) (M.op (τ X0) (τ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq8588 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq8588
    | exact resolve eq8588 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8588
  have eq25392 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (σ (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq25151 X0 X1
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq25151
    | exact resolve eq25151 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq25151
  have eq30915 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) X1)) = (M.op (σ (M.op X1 X1)) (σ (σ (M.op (M.op X2 (τ (M.op (M.op X0 X1) X1))) (τ (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15568 X1 X0 (σ (σ (M.op (M.op X2 (τ (M.op (M.op X0 X1) X1))) (τ (M.op (M.op (M.op X0 X1) X1) (M.op (M.op X0 X1) X1))))))
       have i₂ := eq25392 (M.op (M.op X0 X1) X1) X2
       grind)
    | exact superpose eq25392 eq15568
    | exact resolve eq15568 eq25392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15568 eq25392
  have eq30991 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X1) X1)) = (M.op (σ (M.op X1 X1)) (σ (M.op X1 (M.op X1 (M.op (M.op X0 X1) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq30915 X0 X1 x
       have i₂ := eq1051 (M.op X0 X1) X1 x
       grind)
    | exact superpose eq1051 eq30915
    | exact resolve eq30915 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq30915
  have eq31041 : ∀ X0 X1 : G, (M.op (σ (M.op X1 X1)) (σ X1)) = (σ (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq30991 X0 X1
       have i₂ := eq216 X1 X1 X0
       grind)
    | exact superpose eq216 eq30991
    | exact resolve eq30991 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq30991
  have eq97301 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq121 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq121
    | exact resolve eq121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq97996 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq97301 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq97301
    | (have j0 := eq97301 X0 X1
       grind)
    | exact resolve eq97301 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97301
  have eq155134 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18568 x y
       grind)
    | exact superpose eq18568 eq16
    | (have j1 := eq18568 x y
       grind)
    | exact resolve eq16 eq18568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18568
  have eq444150 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq155134
       have i₂ := eq97996 x y
       grind)
    | exact superpose eq97996 eq155134
    | (have j1 := eq97996 x y
       grind)
    | (have r₁ := eq155134
       have r₂ := eq97996 x y
       grind)
    | (have r₁ := eq155134
       have r₂ := eq97996 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq155134
       have r₂ := eq97996 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq155134 eq97996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97996 eq155134
  have eq444152 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq444150
  have eq444153 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq444152
  have eq444415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq31041 y y
       have i₂ := eq444153
       grind)
    | exact superpose eq444153 eq31041
    | exact resolve eq31041 eq444153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31041 eq444153
  have eq450358 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq444415
       grind)
    | exact superpose eq444415 eq16
    | (have r₁ := eq16
       have r₂ := eq444415
       grind)
    | exact resolve eq16 eq444415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444415
  have eq450560 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq450358
  have eq450634 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq450560
       grind)
    | exact superpose eq450560 eq10
    | exact resolve eq10 eq450560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450560
  have eq450834 : x = y ∨ x = y := by
    first
    | (have i₁ := eq450634
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq450634
    | exact resolve eq450634 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450634
  have eq450835 : x = y := by grind
  clear eq450834
  have eq450845 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq450835
       grind)
    | exact superpose eq450835 eq16
    | exact resolve eq16 eq450835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450835
  have eq450846 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq450845
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq450845
    | (have r₁ := eq450845
       have r₂ := eq23 x
       grind)
    | exact resolve eq450845 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq450845
  have eq450847 : False := by grind
  exact eq450847
