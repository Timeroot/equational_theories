import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq57 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq537 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq54 X2 X3 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq641 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq57 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq54 X2 X3 X0
       grind)
    | exact superpose eq54 eq57
    | exact resolve eq57 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq57
  have eq8225 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq537 X1 x X2 x
       have i₂ := eq641 X1 x X2 x X0
       grind)
    | exact superpose eq641 eq537
    | exact resolve eq537 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq8895 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8225 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq537 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq537 eq8225
    | exact resolve eq8225 eq537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537 eq8225
  have eq9963 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8895 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq8895
    | (have j0 := eq8895 x X0 y
       grind)
    | exact resolve eq8895 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9964 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq27 eq8895
    | (have j0 := eq8895 (σ x) X0 (σ y)
       grind)
    | exact resolve eq8895 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29579 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq29580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq29579
    | exact resolve eq29579 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29579
  have eq29590 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq29580
       have r₂ := eq28
       grind)
    | exact resolve eq29580 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29580
  have eq29593 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq29590
    | exact resolve eq29590 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29590
  have eq29738 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq29593 eq8895
    | exact resolve eq8895 eq29593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29593
  have eq29741 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq9964 eq29738
    | exact resolve eq29738 eq9964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9964 eq29738
  have eq29742 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29741
  have eq29887 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (M.op X0 X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8895 x X0 x
       have i₂ := eq29742
       grind)
    | exact superpose eq29742 eq8895
    | exact resolve eq8895 eq29742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8895 eq29742
  have eq29890 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9963 eq29887
    | exact resolve eq29887 eq9963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9963 eq29887
  have eq29891 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq29890
  have eq29945 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq29891 eq30
    | exact resolve eq30 eq29891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq29891
  have eq30043 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq29945
    | exact resolve eq29945 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq29945
  have eq30044 : x = y := by grind
  clear eq30043
  have eq30208 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq30044
       grind)
    | exact superpose eq30044 eq19
    | exact resolve eq19 eq30044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq30209 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq30044
       grind)
    | exact superpose eq30044 eq25
    | exact resolve eq25 eq30044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq30044
  have eq30316 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq30209
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30209
    | exact resolve eq30209 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq30209
  have eq30331 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq30316 eq27
    | exact resolve eq27 eq30316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30316
  have eq30700 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq30331 eq69
    | exact resolve eq69 eq30331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq30331
  have eq30872 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq30700
       have i₂ := eq30208
       grind)
    | exact superpose eq30208 eq30700
    | exact resolve eq30700 eq30208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30208 eq30700
  have eq30885 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30872 eq15
    | exact resolve eq15 eq30872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30872
  have eq30930 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq30885
    | exact resolve eq30885 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq30885
  have eq30939 : False := by grind
  exact eq30939

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
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
  have eq181 : ∀ X0 : G, (σ x) = (M.op (M.op (k X0 X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq178
    | exact resolve eq178 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq182 : ∀ X0 : G, x = (M.op (M.op (k X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (k X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq186 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X2 (M.op (M.op X1 X1) (k X2 X2))
       have i₂ := eq16 X0 X1 (k X2 X2)
       grind)
    | exact superpose eq16 eq183
    | exact resolve eq183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq647
    | exact resolve eq647 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X1 x x
       have i₂ := eq652 X0 x x
       grind)
    | (have i₁ := eq652 X0 X1 X1
       have i₂ := eq652 (k X1 X1) X1 x
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X0 X2
       grind)
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X2 X0
       grind)
    | exact superpose eq698 eq186
    | exact resolve eq186 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X1 x (k X1 X1)
       have i₂ := eq698 X0 (M.op (k X1 X1) x)
       grind)
    | (have i₁ := eq186 X1 x (k X1 X1)
       have i₂ := eq698 (M.op (k X1 X1) x) X0
       grind)
    | exact superpose eq698 eq186
    | exact resolve eq186 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq773 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq757
    | exact resolve eq757 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq806 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X1 x (k X1 X1)
       have i₂ := eq762 (M.op (k X1 X1) x) X0
       grind)
    | exact superpose eq762 eq186
    | exact resolve eq186 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq762
  have eq1263 : (M.op x y) ≠ (M.op x x) ∨ x = y ∨ x = (k x y) := by
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
  have eq1264 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1266 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1264
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1264
    | exact resolve eq1264 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1267 : (M.op x y) ≠ (k x x) ∨ x = y ∨ x = (k x y) := by
    first
    | (have i₁ := eq1263
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1263
    | exact resolve eq1263 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1292 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq1293 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1350 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1293
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1293
    | exact resolve eq1293 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293
  have eq1351 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1292
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1292
    | exact resolve eq1292 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1292
  have eq8595 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1351
       grind)
    | exact superpose eq1351 eq40
    | exact resolve eq40 eq1351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq8596 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq8595
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8595
    | exact resolve eq8595 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8595
  have eq8598 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq8596
    | exact resolve eq8596 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8596
  have eq19644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq8598 eq1350
    | exact resolve eq1350 eq8598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19654 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq19644
       have r₂ := eq27
       grind)
    | exact resolve eq19644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19644
  have eq19660 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq19654 eq1266
    | (have r₁ := eq1266
       have r₂ := eq19654
       grind)
    | exact resolve eq1266 eq19654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq19654
  have eq19852 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq19660
  have eq19853 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by grind
  clear eq19852
  have eq23198 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq19853 eq8598
    | exact resolve eq8598 eq19853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8598
  have eq23202 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq19853 eq152
    | exact resolve eq152 eq19853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq19853
  have eq23206 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq23198
  have eq23210 : x = (k x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq29 eq23202
    | exact resolve eq23202 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23202
  have eq23213 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq23210
       have r₂ := eq1267
       grind)
    | exact resolve eq23210 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267 eq23210
  have eq23219 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq23213
       grind)
    | exact superpose eq23213 eq40
    | exact resolve eq40 eq23213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq23213
  have eq23225 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq23219
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23219
    | exact resolve eq23219 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23219
  have eq23232 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23225 eq1350
    | exact resolve eq1350 eq23225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350 eq23225
  have eq23239 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq23232
  have eq23447 : x = (M.op (M.op (M.op x y) y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq23206
       grind)
    | exact superpose eq23206 eq182
    | exact resolve eq182 eq23206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq23489 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (k X1 X1)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq773 X1 x X0
       have i₂ := eq23206
       grind)
    | exact superpose eq23206 eq773
    | exact resolve eq773 eq23206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23491 : ∀ X0 : G, (M.op x y) = (k X0 X0) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq806 X0 x
       have i₂ := eq23206
       grind)
    | exact superpose eq23206 eq806
    | exact resolve eq806 eq23206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23206
  have eq23723 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq23491 eq23489
    | exact resolve eq23489 eq23491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23489 eq23491
  have eq27398 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq23239 eq181
    | exact resolve eq181 eq23239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq27441 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (k X1 X1)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq23239 eq773
    | exact resolve eq773 eq23239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq27443 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq23239 eq806
    | exact resolve eq806 eq23239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq23239
  have eq27667 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27443 eq27441
    | exact resolve eq27441 eq27443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27441 eq27443
  have eq34587 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23723 eq23447
    | exact resolve eq23447 eq23723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23447 eq23723
  have eq34595 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq34587
  have eq50277 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27667 eq27398
    | exact resolve eq27398 eq27667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27398 eq27667
  have eq50285 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq50277
  have eq50295 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq50285 eq27
    | exact resolve eq27 eq50285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50285
  have eq50371 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq50295
       have r₂ := eq34595
       grind)
    | exact resolve eq50295 eq34595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34595 eq50295
  have eq50382 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq50371 eq31
    | exact resolve eq31 eq50371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq50371
  have eq50436 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq50382
    | exact resolve eq50382 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq50382
  have eq50437 : x = y := by grind
  clear eq50436
  have eq50451 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq50437
       grind)
    | exact superpose eq50437 eq18
    | exact resolve eq18 eq50437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq50452 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq50437
       grind)
    | exact superpose eq50437 eq24
    | exact resolve eq24 eq50437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq50437
  have eq50472 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq50452
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50452
    | exact resolve eq50452 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50452
  have eq50473 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq50451
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq50451
    | exact resolve eq50451 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50451
  have eq50474 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq50472 eq26
    | exact resolve eq26 eq50472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq50472
  have eq50522 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq50474
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq50474
    | exact resolve eq50474 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq50474
  have eq50550 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq50473
       grind)
    | exact superpose eq50473 eq39
    | exact resolve eq39 eq50473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq50473
  have eq50882 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq50550
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50550
    | exact resolve eq50550 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq50550
  have eq50965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50522 eq50882
    | exact resolve eq50882 eq50522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50522 eq50882
  have eq51024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq50965
    | exact resolve eq50965 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq50965
  have eq51066 : False := by grind
  exact eq51066

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pxx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq25 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq124 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq13 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq124 (σ X0) (σ X1)
       grind)
    | exact superpose eq124 eq15
    | (have j1 := eq124 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq124 X0 X1
       grind)
    | exact superpose eq124 eq133
    | (have j0 := eq133 X0 X1
       have j1 := eq124 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq133 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq133
  have eq346 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq118 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq118 (σ X1) X0
       grind)
    | exact superpose eq118 eq22
    | exact resolve eq22 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq118
  have eq2200 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq169 x y
       grind)
    | exact superpose eq169 eq16
    | (have j1 := eq169 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq169 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq2215 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2200
  have eq6534 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2215
       grind)
    | exact superpose eq2215 eq10
    | exact resolve eq10 eq2215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2215
  have eq6547 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6534
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6534
    | exact resolve eq6534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534
  have eq6548 : x = y := by grind
  clear eq6547
  have eq16331 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6548
       grind)
    | exact superpose eq6548 eq16
    | exact resolve eq16 eq6548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6548
  have eq16332 : False := by grind
  exact eq16332

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
  have eq1259 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
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
  have eq1260 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4232 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1259
       grind)
    | exact superpose eq1259 eq39
    | exact resolve eq39 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq4233 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq4232
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4232
    | exact resolve eq4232 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232
  have eq4235 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq4233
    | exact resolve eq4233 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4233
  have eq14082 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq4235 eq1260
    | exact resolve eq1260 eq4235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14089 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq14082
       have r₂ := eq27
       grind)
    | exact resolve eq14082 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14082
  have eq14095 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14089 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14089
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14089
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14089
       grind)
    | exact resolve eq12 eq14089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14089
  have eq14105 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq14095
  have eq14110 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq14105
       have r₂ := eq26
       grind)
    | exact resolve eq14105 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14105
  have eq14113 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq4235 eq14110
    | exact resolve eq14110 eq4235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4235 eq14110
  have eq14115 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq14113
       have r₂ := eq27
       grind)
    | exact resolve eq14113 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14113
  have eq14118 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq14115
       grind)
    | exact superpose eq14115 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq14115
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq14115
       grind)
    | exact resolve eq12 eq14115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14115
  have eq14128 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq14118
  have eq14133 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14128
       have r₂ := eq18
       grind)
    | exact resolve eq14128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14128
  have eq14137 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq14133
       grind)
    | exact superpose eq14133 eq39
    | exact resolve eq39 eq14133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14133
  have eq14138 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq14137
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14137
    | exact resolve eq14137 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14137
  have eq14140 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq14138
    | exact resolve eq14138 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14138
  have eq14149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14140 eq1260
    | exact resolve eq1260 eq14140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq14153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14149
  have eq14158 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq14153
       have r₂ := eq27
       grind)
    | exact resolve eq14153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14153
  have eq14172 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14158 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14158
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14158
       grind)
    | exact resolve eq12 eq14158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14158
  have eq14182 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq14172
  have eq14187 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq14182
       have r₂ := eq26
       grind)
    | exact resolve eq14182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14182
  have eq14190 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq14140 eq14187
    | exact resolve eq14187 eq14140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14140 eq14187
  have eq14193 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq14190
       have r₂ := eq27
       grind)
    | exact resolve eq14190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14190
  have eq14196 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq14193 eq31
    | exact resolve eq31 eq14193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14193
  have eq14223 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq14196
    | exact resolve eq14196 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14196
  have eq14224 : x = y := by grind
  clear eq14223
  have eq14226 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14224
       grind)
    | exact superpose eq14224 eq18
    | exact resolve eq18 eq14224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14227 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq14224
       grind)
    | exact superpose eq14224 eq24
    | exact resolve eq24 eq14224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14224
  have eq14242 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq14227
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14227
    | exact resolve eq14227 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14227
  have eq14243 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq14226
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq14226
    | exact resolve eq14226 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14226
  have eq14244 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14242 eq26
    | exact resolve eq26 eq14242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14242
  have eq14272 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq14244
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq14244
    | exact resolve eq14244 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq14244
  have eq14276 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq14243
       grind)
    | exact superpose eq14243 eq39
    | exact resolve eq39 eq14243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq14243
  have eq14517 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq14276
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14276
    | exact resolve eq14276 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14276
  have eq14578 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14272 eq14517
    | exact resolve eq14517 eq14272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14272 eq14517
  have eq14621 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq14578
    | exact resolve eq14578 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14578
  have eq14653 : False := by grind
  exact eq14653

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxy_pxx_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq104 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq104 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq104 eq104
    | exact resolve eq104 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq120 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq113
    | exact resolve eq113 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq113
  have eq430 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq840 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op (M.op X1 X1) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (M.op (σ X2) (σ X0)) = (σ (k X2 X0)) ∨ (σ X0) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X2) X1 (σ X0)
       have i₂ := eq430 X2 X0
       grind)
    | (have i₁ := eq9 (σ X1) X1 (σ X1)
       have i₂ := eq430 X0 X1
       grind)
    | exact superpose eq430 eq9
    | (have j1 := eq430 X2 X0
       grind)
    | exact resolve eq9 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq843 : ∀ X0 X2 : G, (σ X0) = (σ X2) ∨ (M.op (σ X2) (σ X0)) = (σ (k X2 X0)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq840 X0 x X2
       have i₂ := eq9 (σ X0) x (σ X0)
       grind)
    | exact superpose eq9 eq840
    | (have j0 := eq840 X0 x X2
       grind)
    | exact resolve eq840 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq844 : ∀ X0 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X2 X0)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have j0 := eq843 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq11591 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq844 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq844
    | (have j0 := eq844 (τ X0) (τ X1)
       grind)
    | exact resolve eq844 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq11621 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11591 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11591
    | (have j0 := eq11591 X0 X1
       grind)
    | exact resolve eq11591 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11591
  have eq11634 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11621 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11621
    | (have j0 := eq11621 X0 X1
       grind)
    | exact resolve eq11621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11621
  have eq11635 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11634 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11634
    | (have j0 := eq11634 X0 X1
       grind)
    | exact resolve eq11634 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11634
  have eq11636 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11635 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11635
    | (have j0 := eq11635 X0 X1
       grind)
    | exact resolve eq11635 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11635
  have eq11637 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11636 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11636
    | (have j0 := eq11636 X0 X1
       grind)
    | exact resolve eq11636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11636
  have eq11640 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq844 X1 X0
       have i₂ := eq11637 X0 X1
       grind)
    | exact superpose eq11637 eq844
    | (have j0 := eq844 X0 X1
       have j1 := eq11637 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq844 eq11637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844 eq11637
  have eq3563972 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11640 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11640
  have eq3564778 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq3563972 x y
       grind)
    | exact superpose eq3563972 eq16
    | (have j1 := eq3563972 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3563972 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3563972 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq3563972 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq3563972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563972
  have eq3565055 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq3564778
  have eq3565079 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3565055
       grind)
    | exact superpose eq3565055 eq10
    | exact resolve eq10 eq3565055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3565055
  have eq3565246 : x = y ∨ x = y := by
    first
    | (have i₁ := eq3565079
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3565079
    | exact resolve eq3565079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3565079
  have eq3565247 : x = y := by grind
  clear eq3565246
  have eq3565248 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3565247
       grind)
    | exact superpose eq3565247 eq16
    | exact resolve eq16 eq3565247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3565247
  have eq3565249 : False := by grind
  exact eq3565249

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq55 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq77 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq76
    | exact resolve eq76 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq77
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq77
    | exact resolve eq77 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq86 : y ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y y) := by
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
  have eq87 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq98 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq94
  have eq99 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq98
  have eq130 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq16
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq379 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op X1 X1) (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq744 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op X2 X2) (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X2 (σ X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq14
    | (have j1 := eq70 X0 X1
       grind)
    | exact resolve eq14 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq78 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1647 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1646
    | exact resolve eq1646 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1650 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1647
       have r₂ := eq28
       grind)
    | exact resolve eq1647 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1652 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1650
    | exact resolve eq1650 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650
  have eq1655 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1652 eq87
    | (have r₁ := eq87
       have r₂ := eq1652
       grind)
    | exact resolve eq87 eq1652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq1652
  have eq1658 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1655
  have eq1659 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1658
  have eq1716 : (k x y) = (τ (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1659 eq61
    | exact resolve eq61 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq1659
  have eq1723 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq130 eq1716
    | exact resolve eq1716 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq1716
  have eq1726 : (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1723
       have r₂ := eq86
       grind)
    | exact resolve eq1723 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq1723
  have eq1784 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1726
       grind)
    | exact superpose eq1726 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1785 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1784
  have eq1787 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1785
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1785
    | exact resolve eq1785 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785
  have eq1790 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1787
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1787
    | exact resolve eq1787 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq1869 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 y
       have i₂ := eq1790
       grind)
    | exact superpose eq1790 eq14
    | exact resolve eq14 eq1790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1790
  have eq1870 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq55 eq1869
    | exact resolve eq1869 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1869
  have eq1871 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1870
  have eq1886 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1871 eq30
    | exact resolve eq30 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871
  have eq1907 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1886
    | exact resolve eq1886 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886
  have eq1908 : y = (M.op x y) ∨ x = y := by grind
  clear eq1907
  have eq1911 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1908 eq21
    | exact resolve eq21 eq1908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1908
  have eq1933 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1911
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1911
    | exact resolve eq1911 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq24566 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) (σ y)) (σ (M.op y y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq744 x y X0
       have i₂ := eq1726
       grind)
    | exact superpose eq1726 eq744
    | (have j0 := eq744 x y x
       grind)
    | exact resolve eq744 eq1726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744 eq1726
  have eq24768 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24566 x
       have i₂ := eq379 y x
       grind)
    | exact superpose eq379 eq24566
    | exact resolve eq24566 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq24566
  have eq24769 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24768
  have eq24850 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24769
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24769
    | exact resolve eq24769 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24769
  have eq24924 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24850
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24850
    | exact resolve eq24850 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24850
  have eq24925 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq24924
  have eq24974 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24925
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24925
    | exact resolve eq24925 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24925
  have eq25020 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24974
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq24974
    | exact resolve eq24974 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24974
  have eq25062 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq25020
    | exact resolve eq25020 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25020
  have eq25089 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq25062 eq28
    | exact resolve eq28 eq25062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25062
  have eq25102 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq25089
       have r₂ := eq1933
       grind)
    | exact resolve eq25089 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1933 eq25089
  have eq25105 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq25102 eq30
    | exact resolve eq30 eq25102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq25102
  have eq25255 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq25105
    | exact resolve eq25105 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq25105
  have eq25256 : x = y := by grind
  clear eq25255
  have eq25259 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq25256
       grind)
    | exact superpose eq25256 eq19
    | exact resolve eq19 eq25256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq25260 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq25256
       grind)
    | exact superpose eq25256 eq25
    | exact resolve eq25 eq25256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq25256
  have eq25292 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25260
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25260
    | exact resolve eq25260 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq25260
  have eq25412 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq25292 eq27
    | exact resolve eq27 eq25292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25292
  have eq25660 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq25412 eq69
    | exact resolve eq69 eq25412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq25412
  have eq25794 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq25660
       have i₂ := eq25259
       grind)
    | exact superpose eq25259 eq25660
    | exact resolve eq25660 eq25259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25259 eq25660
  have eq25800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq25794 eq15
    | exact resolve eq15 eq25794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25794
  have eq25841 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq25800
    | exact resolve eq25800 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25800
  have eq25850 : False := by grind
  exact eq25850

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_x_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28
    | exact resolve eq28 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq34 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq36 : (M.op x y) = (M.op x (τ (σ y))) := by
    first
    | (have i₁ := eq19
       have i₂ := eq34
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq34
  have eq38 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq36
       have i₂ := eq33
       grind)
    | exact superpose eq33 eq36
    | exact resolve eq36 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq36
  have eq40 : (M.op x y) ≠ (τ (σ x)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq38 eq12
    | (have j0 := eq12 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq12 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq43 : ∀ X1 X4 X5 : G, (M.op (M.op X1 X4) (M.op X4 X5)) = X4 := by
    intro X1 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X1) (M.op X1 x) X5
       have i₂ := eq9 X1 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X1 X3 X4 : G, (M.op X1 X3) = (M.op X1 (M.op (M.op X1 X3) X4)) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq9 (M.op X1 X3) (M.op x x) X1 X4
       have i₂ := eq9 X1 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq38 eq14
    | (have j0 := eq14 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq14 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq50 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq57 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq58 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq59 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq57 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq62 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq38 eq43
    | exact resolve eq43 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op X0 (τ (σ x))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq38 eq43
    | exact resolve eq43 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X3 (M.op X2 X0)) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq43 X3 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq43 X2 X0 x
       grind)
    | exact superpose eq43 eq43
    | exact resolve eq43 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k (M.op X0 X1) (M.op X2 X0)) = X0 ∨ (M.op X2 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op x x) (M.op X1 x)
       have i₂ := eq43 X1 x x
       grind)
    | exact superpose eq43 eq14
    | (have j0 := eq14 (M.op X0 X1) (M.op X2 X0)
       grind)
    | exact resolve eq14 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op X2 X0) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X1) (M.op X2 X0)
       have i₂ := eq43 X2 X0 X1
       grind)
    | exact superpose eq43 eq12
    | (have j0 := eq12 (M.op X0 X1) (M.op X2 X0)
       grind)
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X1 : G, (M.op x y) = (M.op (M.op X1 (M.op x y)) (τ (σ y))) := by
    intro X1
    first
    | exact superpose eq62 eq43
    | exact resolve eq43 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq83 eq12
    | (have j0 := eq12 (τ (σ y)) (M.op X0 (M.op x y))
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op x y) = (M.op (τ (σ x)) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq65 eq43
    | exact resolve eq43 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq41
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq148 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 (M.op (k X0 X1) X2)) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X1 X0 x
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq44
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X1 X2) X0)) = X1 ∨ (M.op X1 X2) = (k (M.op (M.op X1 X2) X0) X1) ∨ (M.op X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 x) x) X1
       have i₂ := eq44 X1 x x
       grind)
    | exact superpose eq44 eq14
    | (have j0 := eq14 (M.op (M.op X1 X2) X0) X1
       grind)
    | exact resolve eq14 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ X1 ∨ (M.op (M.op X1 X2) X0) = (k (M.op (M.op X1 X2) X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X1 X2) X0) X1
       have i₂ := eq44 X1 X2 X0
       grind)
    | exact superpose eq44 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | exact resolve eq12 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq169 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq128
    | exact resolve eq128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq188 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
    first
    | (have i₁ := eq48
       have i₂ := eq14 (τ sF3) (τ sF3)
       grind)
    | exact superpose eq14 eq48
    | (have j1 := eq14 (τ (σ y)) (τ (σ y))
       grind)
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) := by grind
  have eq194 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq196 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq194
  have eq197 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by grind
  clear eq188
  have eq202 : (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq38 eq190
    | exact resolve eq190 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq203 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq202
  have eq224 : ∀ X0 : G, (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 (M.op x x)
       have i₂ := eq43 x x x
       grind)
    | exact superpose eq43 eq58
    | exact resolve eq58 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq51 (σ (M.op X0 X0)) (σ X0)
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq51
    | (have j0 := eq51 (σ (M.op X0 X0)) (σ X0)
       have j1 := eq58 X0
       grind)
    | (have r₁ := eq51 (σ (M.op X0 X0)) (σ X0)
       have r₂ := eq58 X0
       grind)
    | exact resolve eq51 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq228 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq226 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq242 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq51 (k X0 X0) X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq51
    | (have j0 := eq51 (k X0 X0) X0
       have j1 := eq59 X0
       grind)
    | (have r₁ := eq51 (k X0 X0) X0
       have r₂ := eq59 X0
       grind)
    | exact resolve eq51 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq244 : ∀ X0 : G, (k X0 X0) ≠ (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq242 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq245 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq262 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 (M.op X0 X1)) ∨ (k X1 (M.op X2 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X2 (M.op X0 X1))
       have i₂ := eq67 X1 X0 X2
       grind)
    | exact superpose eq67 eq12
    | (have j0 := eq12 X1 (M.op X2 (M.op X0 X1))
       grind)
    | exact resolve eq12 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ X0) (τ X0))) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq224 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq224
    | (have j0 := eq224 (τ X0)
       grind)
    | exact resolve eq224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq395 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq203 eq15
    | exact resolve eq15 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq398 : (σ x) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq395
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq395
    | exact resolve eq395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq399 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq398
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq398
    | exact resolve eq398 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq515 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43 (k X0 X0) X0 X1
       have i₂ := eq245 X0
       grind)
    | exact superpose eq245 eq43
    | (have j1 := eq245 X0
       grind)
    | exact resolve eq43 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq610 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq69 X0 X0 X1
       have i₂ := eq43 X0 X0 X0
       grind)
    | exact superpose eq43 eq69
    | (have j0 := eq69 X0 X0 X1
       grind)
    | exact resolve eq69 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) (M.op X0 X1)) = X1 ∨ (M.op X1 X2) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 X1 X2 (M.op X1 X2)
       have i₂ := eq69 X1 X2 X0
       grind)
    | exact superpose eq69 eq44
    | (have j1 := eq69 X1 X2 X0
       grind)
    | exact resolve eq44 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X0 X1) ∨ (M.op X1 X2) = (k (M.op X1 X2) (M.op X1 X2)) ∨ (k (M.op X1 X2) (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 X2) (M.op X1 X2)
       have i₂ := eq69 X1 X2 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (M.op X1 X2) (M.op X1 X2)
       have j1 := eq69 X1 X2 X0
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have r₂ := eq69 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
       grind)
    | (have r₁ := eq12 (M.op X2 X2) (M.op X2 X2)
       have r₂ := eq69 X2 X2 X2
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq69 X0 X1 X0
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq658 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq610 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq692 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq658 (M.op X0 X0) X1
       have i₂ := eq43 X0 X0 X0
       grind)
    | exact superpose eq43 eq658
    | (have j0 := eq658 (M.op X0 X0) X1
       grind)
    | exact resolve eq658 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : (M.op x y) = (k (M.op (M.op x y) (M.op x y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq65 eq658
    | exact resolve eq658 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq706 : (τ (σ y)) = (k (M.op (τ (σ y)) (τ (σ y))) (M.op x y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq38 eq658
    | exact resolve eq658 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq705 eq15
    | exact resolve eq15 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq742 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have i₁ := eq740
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq740
    | exact resolve eq740 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq743 : (σ (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq21 eq742
    | exact resolve eq742 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq745 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq743 eq148
    | (have j0 := eq148 (σ (M.op (M.op x y) (M.op x y))) (σ x) x
       grind)
    | exact resolve eq148 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq767 : (σ (τ (σ y))) = (k (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq706 eq15
    | exact resolve eq15 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq769 : (σ (τ (σ y))) = (k (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq21 eq767
    | exact resolve eq767 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq770 : (σ y) = (k (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op x y))) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq769
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq769
    | exact resolve eq769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq828 : (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by
    first
    | exact superpose eq197 eq12
    | (have j0 := eq12 (τ (σ y)) (τ (σ y))
       grind)
    | (have r₁ := eq12 (τ (σ y)) (τ (σ y))
       have r₂ := eq197
       grind)
    | exact resolve eq12 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq841 : (τ (σ y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by grind
  clear eq828
  have eq903 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op X2 X0) X2) ∨ (M.op X2 X0) = (k (M.op (M.op X2 X0) X1) X2) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44 (M.op X2 X0) X1 (M.op (M.op X2 X0) X1)
       have i₂ := eq161 X1 X2 X0
       grind)
    | exact superpose eq161 eq44
    | (have j1 := eq161 X1 X2 X0
       grind)
    | exact resolve eq44 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k (M.op (M.op X2 X0) X1) X2) ∨ (M.op (M.op X2 X0) X1) = (M.op X2 X1) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X1 (M.op X2 X0) (M.op (M.op X2 X0) X1)
       have i₂ := eq161 X1 X2 X0
       grind)
    | exact superpose eq161 eq67
    | (have j1 := eq161 X1 X2 X0
       grind)
    | exact resolve eq67 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : ∀ X0 X1 X2 : G, (k (M.op (M.op X2 X0) X1) X2) = X2 ∨ (M.op X2 (M.op (M.op X2 X0) X1)) = X2 ∨ (M.op X2 X0) = (k (M.op (M.op X2 X0) X1) X2) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    grind
  clear eq161
  have eq933 : ∀ X0 X1 X2 : G, (M.op X2 X0) = X2 ∨ (k (M.op (M.op X2 X0) X1) X2) = X2 ∨ (M.op X2 X0) = (k (M.op (M.op X2 X0) X1) X2) ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq910 X0 X1 X2
       have i₂ := eq44 X2 X0 X1
       grind)
    | (have i₁ := eq910 X0 X1 X1
       have i₂ := eq44 X1 (M.op (M.op X1 X0) X1) x
       grind)
    | exact superpose eq44 eq910
    | (have j0 := eq910 X0 X1 X2
       grind)
    | exact resolve eq910 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq934 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k (M.op (M.op X2 X0) X1) X2) ∨ (k (M.op (M.op X2 X0) X1) X2) = X2 ∨ (M.op X2 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq933 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq973 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq228 X0
       grind)
    | exact superpose eq228 eq12
    | (have j0 := eq12 (σ X0) (σ (M.op X0 X0))
       have j1 := eq228 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ (M.op X0 X0))
       have r₂ := eq228 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq228 X0
       grind)
    | exact resolve eq12 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq988 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k (σ X0) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq973 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1138 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | exact superpose eq770 eq148
    | (have j0 := eq148 (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op x y)) x
       grind)
    | exact resolve eq148 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq1178 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq399 eq15
    | exact resolve eq15 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq1187 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1178
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq1178
    | exact resolve eq1178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1188 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1187
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq1187
    | exact resolve eq1187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1189 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq1188
    | exact resolve eq1188 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1195 : (τ (σ x)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1189 eq169
    | exact resolve eq169 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189
  have eq1585 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (τ X0) (M.op (τ X0) (τ X0)) x
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq44
    | (have j1 := eq300 X0
       grind)
    | exact resolve eq44 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1593 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (M.op (τ X0) X1) = (k (M.op (τ X0) X1) (τ X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq162 X0 (τ X0) (M.op (τ X0) (τ X0))
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq162
    | (have j1 := eq300 X0
       grind)
    | (have r₁ := eq162 X0 (τ X0) (M.op (τ X0) (τ X0))
       have r₂ := eq300 X0
       grind)
    | exact resolve eq162 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq300
  have eq1596 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (k (M.op (τ X0) X1) (τ X0)) ∨ (k (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1593 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1644 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq148 X0 X0 (M.op X0 x)
       have i₂ := eq515 X0 x
       grind)
    | exact superpose eq515 eq148
    | (have j0 := eq148 X0 X0 x
       have j1 := eq515 X0 x
       grind)
    | exact resolve eq148 eq515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq515
  have eq1663 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1644 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1713 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1 X0 X0
       have i₂ := eq1663 X0
       grind)
    | exact superpose eq1663 eq43
    | (have j1 := eq1663 X0
       grind)
    | exact resolve eq43 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1714 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X0 X1
       have i₂ := eq1663 X0
       grind)
    | exact superpose eq1663 eq43
    | (have j1 := eq1663 X0
       grind)
    | exact resolve eq43 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1735 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (τ (σ y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq83 sF0
       have i₂ := eq1663 sF0
       grind)
    | exact superpose eq1663 eq83
    | (have j1 := eq1663 (M.op x y)
       grind)
    | exact resolve eq83 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2091 : ∀ X1 : G, (M.op x y) = (k (τ (σ y)) (M.op X1 (M.op x y))) ∨ (τ (σ y)) = (M.op (M.op x y) (M.op X1 (M.op x y))) ∨ (M.op x y) = (M.op X1 (M.op x y)) := by
    intro X1
    first
    | exact superpose eq62 eq637
    | (have j0 := eq637 X1 (M.op x y) x
       grind)
    | exact resolve eq637 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq637
  have eq2165 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1713 X0 X0
       have i₂ := eq1663 X0
       grind)
    | exact superpose eq1663 eq1713
    | (have j0 := eq1713 X0 x
       have j1 := eq1663 X0
       grind)
    | exact resolve eq1713 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1663 eq1713
  have eq2238 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2165 X0
       have j1 := eq52 X0
       grind)
    | (have r₁ := eq2165 X0
       have r₂ := eq52 X0
       grind)
    | exact resolve eq2165 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165
  have eq3304 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (k X0 X2) = X2 ∨ (M.op X2 X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq934 x (M.op x x) x
       have i₂ := eq43 x x x
       grind)
    | exact superpose eq43 eq934
    | (have j0 := eq934 X0 x X2
       grind)
    | exact resolve eq934 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq5438 : (τ (σ x)) ≠ (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) := by grind
  clear eq841
  have eq5463 : (τ (σ x)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have r₁ := eq5438
       have r₂ := eq196
       grind)
    | exact resolve eq5438 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq5438
  have eq5580 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (k X1 X0)) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X2 X0 X1
       have i₂ := eq3304 X1 X0
       grind)
    | exact superpose eq3304 eq43
    | (have j1 := eq3304 X1 X0
       grind)
    | exact resolve eq43 eq3304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5831 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X2) = X0 ∨ (M.op X2 X0) = (k X0 X2) ∨ (M.op X2 X0) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq903 x (M.op x x) x
       have i₂ := eq43 x x x
       grind)
    | exact superpose eq43 eq903
    | (have j0 := eq903 X0 x X2
       grind)
    | exact resolve eq903 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6050 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X2) ∨ (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq903 X1 X2 X0
       grind)
    | (have i₁ := eq12 X1 (M.op X2 X0)
       have i₂ := eq903 X0 X1 X2
       grind)
    | exact superpose eq903 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       have j1 := eq903 X1 X2 X0
       grind)
    | (have r₁ := eq12 X0 X2
       have r₂ := eq903 X0 X1 X2
       grind)
    | exact resolve eq12 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq7479 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1195 eq51
    | (have j0 := eq51 (τ (σ x)) (τ (σ y))
       grind)
    | (have r₁ := eq51 (τ (σ x)) (τ (σ y))
       have r₂ := eq1195
       grind)
    | exact resolve eq51 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7486 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq7479
  have eq7505 : (M.op x y) = (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq38 eq7486
    | exact resolve eq7486 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7486
  have eq7506 : (τ (σ x)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq7505
  have eq8901 : (σ (τ (σ x))) = (M.op (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq7506 eq988
    | exact resolve eq988 eq7506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq7506
  have eq8973 : (σ (τ (σ x))) = (M.op (σ y) (σ y)) ∨ (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8901
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq8901
    | exact resolve eq8901 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8901
  have eq8982 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8973
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq8973
    | exact resolve eq8973 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8973
  have eq8985 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8982
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq8982
    | exact resolve eq8982 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8982
  have eq8987 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8985
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq8985
    | exact resolve eq8985 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8985
  have eq8989 : (M.op x y) = (τ (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq38 eq8987
    | exact resolve eq8987 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8987
  have eq8990 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq8989
  have eq12236 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq644 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq12240 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12236 X0
       have j1 := eq70 X0 X0 X0
       grind)
    | (have r₁ := eq12236 X0
       have r₂ := eq70 X0 x X0
       grind)
    | exact resolve eq12236 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq12236
  have eq28260 : (σ (τ (σ x))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq5463 eq15
    | exact resolve eq15 eq5463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5463
  have eq28302 : (σ (τ (σ x))) = (k (σ y) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq28260
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq28260
    | exact resolve eq28260 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28260
  have eq28307 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq28302
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq28302
    | exact resolve eq28302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28302
  have eq28310 : (M.op x y) = (τ (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq28307 eq1195
    | exact resolve eq1195 eq28307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq28307
  have eq28331 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq28310
  have eq28715 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq28331 eq2238
    | (have j0 := eq2238 (σ y)
       grind)
    | exact resolve eq2238 eq28331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2238
  have eq31357 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq904 X0 x x
       have i₂ := eq5831 X0 x
       grind)
    | exact superpose eq5831 eq904
    | (have j0 := eq904 X1 X1 X0
       have j1 := eq5831 X1 X0
       grind)
    | exact resolve eq904 eq5831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq5831
  have eq31518 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31357 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31357
  have eq32641 : ∀ X0 X1 : G, (k (M.op X0 X1) (k X0 X0)) = X0 ∨ (M.op X0 X1) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31518 (k X0 X0) (M.op X0 X1)
       have i₂ := eq1714 X0 X1
       grind)
    | exact superpose eq1714 eq31518
    | (have j0 := eq31518 X0 X0
       have j1 := eq1714 X0 X1
       grind)
    | exact resolve eq31518 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq32661 : (M.op x y) = (k (τ (σ y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ y)) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1735 eq31518
    | (have j0 := eq31518 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq31518 eq1735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735
  have eq33019 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31518 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33252 : (M.op x y) = (k (τ (σ y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ y)) = (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq52 (M.op x y)
       grind)
    | (have r₁ := eq32661
       have r₂ := eq52 (M.op x y)
       grind)
    | exact resolve eq32661 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32661
  have eq33261 : ∀ X0 X1 : G, (k (M.op X0 X1) (k X0 X0)) = X0 ∨ (M.op X0 X1) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq32641 X0 X1
       have j1 := eq52 X0
       grind)
    | (have r₁ := eq32641 X0 X1
       have r₂ := eq52 X0
       grind)
    | exact resolve eq32641 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq32641
  have eq58460 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq8990 eq169
    | exact resolve eq169 eq8990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8990
  have eq58511 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq58460
       have r₂ := eq40
       grind)
    | exact resolve eq58460 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq58460
  have eq59660 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq58511 eq15
    | exact resolve eq15 eq58511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58511
  have eq59719 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq59660
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq59660
    | exact resolve eq59660 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59660
  have eq59725 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq59719
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq59719
    | exact resolve eq59719 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59719
  have eq59730 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq59725 eq51
    | (have j0 := eq51 (σ x) (σ y)
       grind)
    | exact resolve eq51 eq59725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59780 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq59730
  have eq60212 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq28715 eq12
    | (have j0 := eq12 (σ y) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq28715
       grind)
    | exact resolve eq12 eq28715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28715
  have eq60275 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq60212
  have eq65001 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq60275 eq28331
    | exact resolve eq28331 eq60275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60275
  have eq65113 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq65001
  have eq65285 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq65113 eq31518
    | exact resolve eq31518 eq65113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31518 eq65113
  have eq65288 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq65285
  have eq65463 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq65288
  have eq88451 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12240 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12240
  have eq88525 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq88451 X0
       have j1 := eq658 X0 X0
       grind)
    | (have r₁ := eq88451 X0
       have r₂ := eq658 X0 X0
       grind)
    | exact resolve eq88451 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq88451
  have eq88860 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq88525 (M.op x x)
       have i₂ := eq43 x x x
       grind)
    | exact superpose eq43 eq88525
    | exact resolve eq88525 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89117 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq14
    | (have j0 := eq14 X0 X1
       grind)
    | exact resolve eq14 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89119 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (k X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq88860 X1
       grind)
    | exact superpose eq88860 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq89183 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X1 (k X0 X0))) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 X1
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq692
    | (have j0 := eq692 X0 X1
       grind)
    | exact resolve eq692 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq92884 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (k X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33019 X0 X1
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq33019
    | (have j0 := eq33019 X0 X1
       grind)
    | exact resolve eq33019 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33019
  have eq92932 : ∀ X0 X1 : G, (k X0 X0) = X0 ∨ (k (M.op X0 X1) (k X0 X0)) = X0 ∨ (M.op X0 X1) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33261 X0 X1
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq33261
    | (have j0 := eq33261 X0 X1
       grind)
    | exact resolve eq33261 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33261
  have eq97803 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq88525 X0
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq88525
    | exact resolve eq88525 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88525
  have eq102933 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op (τ (σ y)) (τ (σ y)))) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1138 X0
       have i₂ := eq88860 (σ (M.op (τ sF3) (τ sF3)))
       grind)
    | exact superpose eq88860 eq1138
    | (have j0 := eq1138 X0
       grind)
    | exact resolve eq1138 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq103059 : ∀ X0 : G, (σ x) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq745 X0
       have i₂ := eq88860 (σ (M.op sF0 sF0))
       grind)
    | exact superpose eq88860 eq745
    | (have j0 := eq745 X0
       grind)
    | exact resolve eq745 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq103635 : ∀ X0 X1 : G, (k (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1585 X0 X1
       have i₂ := eq88860 (τ X0)
       grind)
    | exact superpose eq88860 eq1585
    | (have j0 := eq1585 X0 X1
       grind)
    | exact resolve eq1585 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq103638 : ∀ X0 X1 : G, (k (σ (k (τ X0) (τ X0))) X0) = X0 ∨ (M.op (τ X0) X1) = (k (M.op (τ X0) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1596 X0 X1
       have i₂ := eq88860 (τ X0)
       grind)
    | exact superpose eq88860 eq1596
    | (have j0 := eq1596 X0 X1
       grind)
    | exact resolve eq1596 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq106371 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (τ (σ y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq33252
       have i₂ := eq88860 (k sF0 sF0)
       grind)
    | exact superpose eq88860 eq33252
    | exact resolve eq33252 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33252
  have eq108436 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq59725
       have i₂ := eq88860 sF3
       grind)
    | exact superpose eq88860 eq59725
    | exact resolve eq59725 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59725
  have eq108454 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq59780
       have i₂ := eq88860 sF3
       grind)
    | exact superpose eq88860 eq59780
    | exact resolve eq59780 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59780
  have eq109606 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (τ (σ y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq106371
       have i₂ := eq88860 sF0
       grind)
    | exact superpose eq88860 eq106371
    | exact resolve eq106371 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106371
  have eq111353 : ∀ X0 X1 : G, (k (k (σ (τ X0)) (σ (τ X0))) X0) = X0 ∨ (M.op (τ X0) X1) = (k (M.op (τ X0) X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq103638 X0 X1
       have i₂ := eq15 (τ X0) (τ X0)
       grind)
    | exact superpose eq15 eq103638
    | (have j0 := eq103638 X0 X1
       grind)
    | exact resolve eq103638 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103638
  have eq111356 : ∀ X0 X1 : G, (k (k (σ (τ X0)) (σ (τ X0))) X0) = X0 ∨ (τ X0) = (M.op (τ X0) (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103635 X0 X1
       have i₂ := eq15 (τ X0) (τ X0)
       grind)
    | exact superpose eq15 eq103635
    | (have j0 := eq103635 X0 X1
       grind)
    | exact resolve eq103635 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103635
  have eq111807 : ∀ X0 : G, (σ x) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq103059 X0
       have i₂ := eq88860 sF0
       grind)
    | exact superpose eq88860 eq103059
    | (have j0 := eq103059 X0
       grind)
    | exact resolve eq103059 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103059
  have eq111927 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (k (τ (σ y)) (τ (σ y)))) (σ (k (τ (σ y)) (τ (σ y))))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq102933 X0
       have i₂ := eq88860 (τ sF3)
       grind)
    | exact superpose eq88860 eq102933
    | (have j0 := eq102933 X0
       grind)
    | exact resolve eq102933 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102933
  have eq119296 : ∀ X0 X1 : G, (M.op X0 X1) = (k (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (k (M.op X0 X1) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq92932 X0 X1
       have i₂ := eq88860 (k X0 X0)
       grind)
    | exact superpose eq88860 eq92932
    | (have j0 := eq92932 X0 X1
       grind)
    | exact resolve eq92932 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92932
  have eq122004 : ∀ X0 X1 : G, (k X0 X0) = (k X0 (M.op X1 (k X0 X0))) ∨ (k X0 X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq89183 X0 X1
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq89183
    | (have j0 := eq89183 X0 X1
       grind)
    | exact resolve eq89183 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89183
  have eq122748 : (M.op x y) = (k (τ (σ y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq109606
       have i₂ := eq97803 sF0
       grind)
    | exact superpose eq97803 eq109606
    | exact resolve eq109606 eq97803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109606
  have eq124090 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (k (M.op (τ X0) X1) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq111353 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq111353
    | (have j0 := eq111353 X0 X1
       grind)
    | exact resolve eq111353 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111353
  have eq124093 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op (τ X0) X1)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq111356 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq111356
    | (have j0 := eq111356 X0 X1
       grind)
    | exact resolve eq111356 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111356
  have eq124460 : ∀ X0 : G, (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq111807 X0
       have i₂ := eq15 sF0 sF0
       grind)
    | exact superpose eq15 eq111807
    | (have j0 := eq111807 X0
       grind)
    | exact resolve eq111807 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111807
  have eq124574 : ∀ X0 : G, (σ (M.op x y)) = (k (k (σ (τ (σ y))) (σ (τ (σ y)))) (k (σ (τ (σ y))) (σ (τ (σ y))))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq111927 X0
       have i₂ := eq15 (τ sF3) (τ sF3)
       grind)
    | exact superpose eq15 eq111927
    | (have j0 := eq111927 X0
       grind)
    | exact resolve eq111927 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111927
  have eq129558 : ∀ X0 X1 : G, (k (M.op X0 X1) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq119296 X0 X1
       have i₂ := eq97803 X0
       grind)
    | exact superpose eq97803 eq119296
    | (have j0 := eq119296 X0 X1
       grind)
    | exact resolve eq119296 eq97803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119296
  have eq133193 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq124460 X0
       have i₂ := eq97803 (σ sF0)
       grind)
    | exact superpose eq97803 eq124460
    | (have j0 := eq124460 X0
       grind)
    | exact resolve eq124460 eq97803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124460
  have eq133305 : ∀ X0 : G, (σ (M.op x y)) = (σ (τ (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq124574 X0
       have i₂ := eq97803 (σ (τ sF3))
       grind)
    | exact superpose eq97803 eq124574
    | (have j0 := eq124574 X0
       grind)
    | exact resolve eq124574 eq97803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124574
  have eq139394 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq21 eq133193
    | (have j0 := eq133193 X0
       grind)
    | exact resolve eq133193 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133193
  have eq139484 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op (τ (σ y)) (τ (σ y))))) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq133305 X0
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq133305
    | (have j0 := eq133305 X0
       grind)
    | exact resolve eq133305 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133305
  have eq143883 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq139394 X0
       have i₂ := eq88860 sF0
       grind)
    | exact superpose eq88860 eq139394
    | (have j0 := eq139394 X0
       grind)
    | exact resolve eq139394 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139394
  have eq143957 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (k (τ (σ y)) (τ (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq139484 X0
       have i₂ := eq88860 (τ sF3)
       grind)
    | exact superpose eq88860 eq139484
    | (have j0 := eq139484 X0
       grind)
    | exact resolve eq139484 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139484
  have eq147251 : ∀ X0 : G, (σ x) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq143883 X0
       have i₂ := eq15 sF0 sF0
       grind)
    | exact superpose eq15 eq143883
    | (have j0 := eq143883 X0
       grind)
    | exact resolve eq143883 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143883
  have eq147321 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (τ (σ y))) (σ (τ (σ y))))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq143957 X0
       have i₂ := eq15 (τ sF3) (τ sF3)
       grind)
    | exact superpose eq15 eq143957
    | (have j0 := eq143957 X0
       grind)
    | exact resolve eq143957 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143957
  have eq150001 : ∀ X0 : G, (σ x) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq21 eq147251
    | (have j0 := eq147251 X0
       grind)
    | exact resolve eq147251 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147251
  have eq150068 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (M.op x y) = (τ (σ y)) := by
    intro X0
    first
    | (have i₁ := eq147321 X0
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq147321
    | (have j0 := eq147321 X0
       grind)
    | exact resolve eq147321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147321
  have eq161267 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43 X0 X0 X1
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq43
    | exact resolve eq43 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq161268 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X0 x
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq44
    | exact resolve eq44 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161270 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X0 x
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq67
    | exact resolve eq67 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161273 : ∀ X0 X1 : G, (k X0 X0) ≠ (M.op X1 (k X0 X0)) ∨ (k X0 (M.op X1 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X0 x
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq262
    | exact resolve eq262 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq161327 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X1 X0)) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5580 X0 X1 X0
       have i₂ := eq88860 X0
       grind)
    | exact superpose eq88860 eq5580
    | (have j0 := eq5580 X0 X1 x
       grind)
    | exact resolve eq5580 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5580
  have eq161349 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (τ (σ y)) = (k (τ (σ y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq97 sF0
       have i₂ := eq88860 sF0
       grind)
    | exact superpose eq88860 eq97
    | exact resolve eq97 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq161357 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1 (M.op X0 X1)
       have i₂ := eq88860 (M.op X0 X1)
       grind)
    | exact superpose eq88860 eq44
    | exact resolve eq44 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq161387 : (M.op x y) = (M.op (τ (σ x)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq105 sF0
       have i₂ := eq88860 sF0
       grind)
    | exact superpose eq88860 eq105
    | exact resolve eq105 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq162276 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq28331 eq161267
    | exact resolve eq161267 eq28331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28331
  have eq165373 : (σ y) = (M.op (σ x) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq162276 eq161357
    | exact resolve eq161357 eq162276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162276
  have eq166172 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq124093 X0 (M.op (τ X0) x)
       have i₂ := eq124093 X0 x
       grind)
    | exact superpose eq124093 eq124093
    | (have j0 := eq124093 X0 x
       have j1 := eq124093 X0 x
       grind)
    | exact resolve eq124093 eq124093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124093
  have eq166258 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq166172 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166172
  have eq166265 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq166258 X0
       have i₂ := eq88860 (τ X0)
       grind)
    | exact superpose eq88860 eq166258
    | (have j0 := eq166258 X0
       grind)
    | exact resolve eq166258 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166258
  have eq166309 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) (σ (τ X0))) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15 (τ X0) (τ X0)
       have i₂ := eq166265 X0
       grind)
    | exact superpose eq166265 eq15
    | (have j1 := eq166265 X0
       grind)
    | exact resolve eq15 eq166265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166265
  have eq166316 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq166309 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq166309
    | (have j0 := eq166309 X0
       grind)
    | exact resolve eq166309 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166309
  have eq167474 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (k (M.op x y) (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq122748 eq15
    | exact resolve eq15 eq122748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122748
  have eq167484 : (σ (M.op x y)) = (k (σ (τ (σ y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq167474
       have i₂ := eq15 sF0 sF0
       grind)
    | exact superpose eq15 eq167474
    | exact resolve eq167474 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167474
  have eq167488 : (σ (M.op x y)) = (k (σ (τ (σ y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq21 eq167484
    | exact resolve eq167484 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167484
  have eq167492 : (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq167488
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq167488
    | exact resolve eq167488 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167488
  have eq171587 : ∀ X0 X1 : G, (σ X0) = (k (k (σ X0) (σ X0)) (σ X0)) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq124090 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq124090
    | (have j0 := eq124090 (σ X0) X1
       grind)
    | exact resolve eq124090 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124090
  have eq173792 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq108436 eq161327
    | (have j0 := eq161327 (σ x) (σ y)
       grind)
    | exact resolve eq161327 eq108436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108436 eq161327
  have eq173946 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq173792
       have r₂ := eq108454
       grind)
    | exact resolve eq173792 eq108454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108454 eq173792
  have eq180356 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (k (σ X0) (σ X0))) (τ (σ X0))) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq169 (σ X0) (k (σ X0) (σ X0))
       have i₂ := eq171587 X0 X1
       grind)
    | exact superpose eq171587 eq169
    | (have j1 := eq171587 X0 X1
       grind)
    | exact resolve eq169 eq171587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171587
  have eq180364 : ∀ X0 X1 : G, (k (τ (k (σ X0) (σ X0))) X0) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq180356 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq180356
    | (have j0 := eq180356 X0 X1
       grind)
    | exact resolve eq180356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180356
  have eq180367 : ∀ X0 X1 : G, (k (k (τ (σ X0)) (τ (σ X0))) X0) = X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq180364 X0 X1
       have i₂ := eq169 (σ X0) (σ X0)
       grind)
    | exact superpose eq169 eq180364
    | (have j0 := eq180364 X0 X1
       grind)
    | exact resolve eq180364 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180364
  have eq180368 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq180367 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq180367
    | (have j0 := eq180367 X0 X1
       grind)
    | exact resolve eq180367 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180367
  have eq180376 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq180368 X0 (M.op (k X0 X0) x)
       have i₂ := eq161268 X0 x
       grind)
    | exact superpose eq161268 eq180368
    | (have j0 := eq180368 X0 x
       grind)
    | exact resolve eq180368 eq161268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180368
  have eq180649 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq180376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180376
  have eq180662 : ∀ X0 : G, (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq180649 X0
       have j1 := eq166316 X0
       grind)
    | (have r₁ := eq180649 X0
       have r₂ := eq166316 X0
       grind)
    | exact resolve eq180649 eq166316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166316 eq180649
  have eq181311 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq180662 (k X0 X0)
       have i₂ := eq97803 X0
       grind)
    | exact superpose eq97803 eq180662
    | exact resolve eq180662 eq97803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189214 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (M.op X0 (M.op x y)))) ∨ (τ (σ y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2091 eq15
    | (have j1 := eq2091 X0
       grind)
    | exact resolve eq15 eq2091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq189244 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ (M.op X0 (M.op x y)))) ∨ (τ (σ y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq189214 X0
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq189214
    | (have j0 := eq189214 X0
       grind)
    | exact resolve eq189214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189214
  have eq189256 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ (M.op X0 (M.op x y)))) ∨ (τ (σ y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq189244
    | (have j0 := eq189244 X0
       grind)
    | exact resolve eq189244 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189244
  have eq193191 : (σ (M.op x y)) = (k (σ y) (σ (k (M.op x y) (M.op x y)))) ∨ (τ (σ y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq189256 (M.op x (k sF0 sF0))
       have i₂ := eq161270 sF0 x
       grind)
    | exact superpose eq161270 eq189256
    | exact resolve eq189256 eq161270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189256
  have eq193250 : (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq193191
       have i₂ := eq15 sF0 sF0
       grind)
    | exact superpose eq15 eq193191
    | exact resolve eq193191 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193191
  have eq193274 : (τ (σ y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21 eq193250
    | exact resolve eq193250 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193250
  have eq193334 : (M.op x y) ≠ (τ (σ y)) ∨ (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq193274 eq12
    | (have j0 := eq12 (k (M.op x y) (M.op x y)) (M.op x y)
       grind)
    | exact resolve eq12 eq193274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193274
  have eq193431 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq193334
       have r₂ := eq167492
       grind)
    | exact resolve eq193334 eq167492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167492 eq193334
  have eq193437 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq193431
       have i₂ := eq180662 sF0
       grind)
    | exact superpose eq180662 eq193431
    | exact resolve eq193431 eq180662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193431
  have eq193438 : (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq193437
  have eq193446 : (τ (σ (M.op x y))) = (k (τ (σ y)) (τ (k (σ (M.op x y)) (σ (M.op x y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq193438 eq169
    | exact resolve eq169 eq193438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193438
  have eq193474 : (τ (σ (M.op x y))) = (k (τ (σ y)) (k (τ (σ (M.op x y))) (τ (σ (M.op x y))))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq193446
       have i₂ := eq169 sF1 sF1
       grind)
    | exact superpose eq169 eq193446
    | exact resolve eq193446 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193446
  have eq193476 : (M.op x y) = (k (τ (σ y)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq32 eq193474
    | exact resolve eq193474 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193474
  have eq337244 : ∀ X0 X2 : G, (M.op X0 X2) ≠ X0 ∨ (k X0 X0) = (k (k X0 X0) X0) ∨ (k (M.op X0 X2) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq6050 (k X0 X0) (M.op X0 x) X2
       have i₂ := eq161267 X0 x
       grind)
    | exact superpose eq161267 eq6050
    | exact resolve eq6050 eq161267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050
  have eq337424 : ∀ X0 X2 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k (M.op X0 X2) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq337244 X0 X2
       have j1 := eq129558 X0 X2
       grind)
    | (have r₁ := eq337244 X0 x
       have r₂ := eq129558 X0 x
       grind)
    | exact resolve eq337244 eq129558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129558 eq337244
  have eq337467 : ∀ X0 X2 : G, (k X0 X0) = X0 ∨ (k (M.op X0 X2) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq337424 X0 X2
       have i₂ := eq180662 X0
       grind)
    | exact superpose eq180662 eq337424
    | (have j0 := eq337424 X0 X2
       grind)
    | exact resolve eq337424 eq180662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180662 eq337424
  have eq337468 : ∀ X0 X2 : G, (k (M.op X0 X2) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq337467 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337467
  have eq338611 : (τ (σ x)) = (k (M.op x y) (k (τ (σ x)) (τ (σ x)))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq161387 eq337468
    | (have j0 := eq337468 (τ (σ x)) x
       grind)
    | exact resolve eq337468 eq161387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161387
  have eq338705 : ∀ X0 : G, (σ x) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | exact superpose eq150001 eq337468
    | (have j0 := eq337468 (σ x) x
       have j1 := eq150001 X0
       grind)
    | exact resolve eq337468 eq150001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150001 eq337468
  have eq338767 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq338705 X0
       have i₂ := eq181311 sF2
       grind)
    | exact superpose eq181311 eq338705
    | (have j0 := eq338705 X0
       grind)
    | exact resolve eq338705 eq181311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338705
  have eq338768 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    intro X0
    first
    | (have j0 := eq338767 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338767
  have eq341591 : (σ (τ (σ x))) = (k (σ (M.op x y)) (σ (k (τ (σ x)) (τ (σ x))))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq338611 eq15
    | exact resolve eq15 eq338611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338611
  have eq341599 : (σ (τ (σ x))) = (k (σ (M.op x y)) (k (σ (τ (σ x))) (σ (τ (σ x))))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq341591
       have i₂ := eq15 (τ sF2) (τ sF2)
       grind)
    | exact superpose eq15 eq341591
    | exact resolve eq341591 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341591
  have eq341600 : (σ x) = (k (σ (M.op x y)) (k (σ x) (σ x))) ∨ (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq341599
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq341599
    | exact resolve eq341599 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341599
  have eq341601 : (τ (σ x)) = (k (τ (σ x)) (τ (σ x))) ∨ (σ x) = (k (σ (M.op x y)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq21 eq341600
    | exact resolve eq341600 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341600
  have eq343826 : (σ (τ (σ x))) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ x) = (k (σ (M.op x y)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq341601 eq15
    | exact resolve eq15 eq341601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341601
  have eq343839 : (σ x) = (k (σ (M.op x y)) (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq343826
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq343826
    | exact resolve eq343826 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343826
  have eq370471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq150068 eq338768
    | exact resolve eq338768 eq150068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150068
  have eq370582 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | (have r₁ := eq370471
       have r₂ := eq31
       grind)
    | exact resolve eq370471 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370471
  have eq372626 : (k (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq370582 eq161270
    | exact resolve eq161270 eq370582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370582
  have eq373153 : (σ (M.op x y)) = (M.op (σ x) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq372626 eq338768
    | exact resolve eq338768 eq372626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338768 eq372626
  have eq373459 : (σ (M.op x y)) = (M.op (σ x) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq373153
  have eq377039 : (σ y) ≠ (M.op (σ x) (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq373459
  have eq378584 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq165373 eq377039
    | (have r₁ := eq377039
       have r₂ := eq165373
       grind)
    | exact resolve eq377039 eq165373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377039
  have eq378606 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq378584
  have eq378607 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq378606
  have eq378649 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq378607 eq65463
    | (have r₁ := eq65463
       have r₂ := eq378607
       grind)
    | exact resolve eq65463 eq378607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65463 eq378607
  have eq378734 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq378649
  have eq378735 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq378734
  have eq379580 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq378735 eq31
    | exact resolve eq31 eq378735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379675 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  have eq379676 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) := by grind
  clear eq378735
  have eq384543 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq379580
       have i₂ := eq3304 sF3 sF2
       grind)
    | exact superpose eq3304 eq379580
    | (have j1 := eq3304 (σ y) (σ x)
       grind)
    | (have r₁ := eq379580
       have r₂ := eq3304 (σ y) (σ x)
       grind)
    | exact resolve eq379580 eq3304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304 eq379580
  have eq384562 : (σ x) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq384543
  have eq384569 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq384562
       have r₂ := eq379675
       grind)
    | exact resolve eq384562 eq379675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379675 eq384562
  have eq384605 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq384569 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq384569
       grind)
    | exact resolve eq12 eq384569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384569
  have eq384884 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq384605
  have eq384916 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq384884
       have r₂ := eq379676
       grind)
    | exact resolve eq384884 eq379676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379676 eq384884
  have eq385110 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq384916 eq11
    | exact resolve eq11 eq384916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384916
  have eq385254 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq385110
    | exact resolve eq385110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385110
  have eq385255 : (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq385254
  have eq385850 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq385255 eq11
    | exact resolve eq11 eq385255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385255
  have eq385885 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq385850
    | exact resolve eq385850 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385850
  have eq385886 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq385885
  have eq386877 : (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq385886 eq38
    | exact resolve eq38 eq385886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq387226 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq386877
       have i₂ := eq88860 (τ sF2)
       grind)
    | exact superpose eq88860 eq386877
    | exact resolve eq386877 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386877
  have eq387315 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq387226 eq15
    | exact resolve eq15 eq387226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387226
  have eq387371 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq387315
       have i₂ := eq11 sF2
       grind)
    | exact superpose eq11 eq387315
    | exact resolve eq387315 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387315
  have eq387390 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq387371
    | exact resolve eq387371 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387371
  have eq387395 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq387390 eq31
    | exact resolve eq31 eq387390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387390
  have eq392107 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq385886 eq387395
    | exact resolve eq387395 eq385886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385886 eq387395
  have eq392129 : (M.op (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq392107
  have eq392133 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq392129
       have r₂ := eq88860 (σ x)
       grind)
    | exact resolve eq392129 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392129
  have eq392782 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq392133 eq31
    | exact resolve eq31 eq392133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392783 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq392133 eq32
    | exact resolve eq32 eq392133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392868 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  have eq394586 : (M.op x y) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq392783 eq193476
    | exact resolve eq193476 eq392783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193476 eq392783
  have eq394649 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq394586
       have i₂ := eq181311 sF0
       grind)
    | exact superpose eq181311 eq394586
    | exact resolve eq394586 eq181311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394586
  have eq394650 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq394649
  have eq397984 : (M.op x y) ≠ (M.op x y) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq394650 eq161349
    | (have r₁ := eq161349
       have r₂ := eq394650
       grind)
    | exact resolve eq161349 eq394650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161349
  have eq398069 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq394650 eq15
    | exact resolve eq15 eq394650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394650
  have eq398093 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq397984
  have eq398094 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq398069
    | exact resolve eq398069 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398069
  have eq399224 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq392133 eq398094
    | exact resolve eq398094 eq392133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399273 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq398094 eq122004
    | exact resolve eq122004 eq398094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122004
  have eq399276 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq398094 eq161268
    | exact resolve eq161268 eq398094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399280 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq398094 eq161273
    | exact resolve eq161273 eq398094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161273 eq398094
  have eq399333 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq399273 X0
       have j1 := eq399280 X0
       grind)
    | (have r₁ := eq399273 X0
       have r₂ := eq399280 X0
       grind)
    | exact resolve eq399273 eq399280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399273 eq399280
  have eq399335 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq399224
       have r₂ := eq392868
       grind)
    | exact resolve eq399224 eq392868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399224
  have eq400206 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq399335 eq165373
    | exact resolve eq165373 eq399335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165373
  have eq400231 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq399335 eq161268
    | exact resolve eq161268 eq399335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161268
  have eq400232 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq399335 eq161270
    | exact resolve eq161270 eq399335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161270 eq399335
  have eq400289 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq400206
       have r₂ := eq392782
       grind)
    | exact resolve eq400206 eq392782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400206
  have eq410811 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq398093 eq15
    | exact resolve eq15 eq398093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398093
  have eq410887 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq410811
    | exact resolve eq410811 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410811
  have eq410890 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq410887
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq410887
    | exact resolve eq410887 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410887
  have eq411810 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq410890 eq92884
    | (have j0 := eq92884 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq92884 eq410890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410890
  have eq411848 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq411810
       have r₂ := eq392133
       grind)
    | exact resolve eq411810 eq392133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411810
  have eq412782 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq399276 eq161357
    | exact resolve eq161357 eq399276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161357 eq399276
  have eq414157 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (τ (M.op X0 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq399333 eq169
    | exact resolve eq169 eq399333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq399333
  have eq414233 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op X0 (σ (M.op x y))))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq32 eq414157
    | exact resolve eq414157 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq414157
  have eq414917 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq400231 eq161267
    | exact resolve eq161267 eq400231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161267 eq400231
  have eq421454 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op X0 (σ y)))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq392133 eq414233
    | exact resolve eq414233 eq392133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414233
  have eq421705 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ (M.op X0 (σ y)))) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq421454 X0
       grind)
    | (have r₁ := eq421454 X0
       have r₂ := eq392868
       grind)
    | exact resolve eq421454 eq392868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392868 eq421454
  have eq422587 : (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq414917 eq421705
    | exact resolve eq421705 eq414917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414917 eq421705
  have eq422716 : (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq422587
  have eq422846 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq422716 eq15
    | exact resolve eq15 eq422716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422716
  have eq422925 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq422846
       have i₂ := eq11 sF3
       grind)
    | exact superpose eq11 eq422846
    | exact resolve eq422846 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422846
  have eq422942 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq422925
    | exact resolve eq422925 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422925
  have eq422997 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq422942 eq92884
    | (have j0 := eq92884 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq92884 eq422942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92884 eq422942
  have eq423034 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq422997
       have r₂ := eq392133
       grind)
    | exact resolve eq422997 eq392133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392133 eq422997
  have eq425333 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq400289 eq31
    | exact resolve eq31 eq400289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400289
  have eq441577 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq411848 eq412782
    | exact resolve eq412782 eq411848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411848 eq412782
  have eq441697 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq441577
  have eq441765 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq441697 eq67
    | exact resolve eq67 eq441697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq441697
  have eq450721 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq423034 eq441765
    | exact resolve eq441765 eq423034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423034 eq441765
  have eq450975 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq450721
  have eq450998 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq450975
       have i₂ := eq88860 sF3
       grind)
    | exact superpose eq88860 eq450975
    | exact resolve eq450975 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450975
  have eq450999 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq450998
  have eq451164 : (σ x) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq450999
  have eq566074 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq425333
       have i₂ := eq89117 sF3 sF2
       grind)
    | exact superpose eq89117 eq425333
    | (have j1 := eq89117 (σ y) (σ x)
       grind)
    | (have r₁ := eq425333
       have r₂ := eq89117 (σ y) (σ x)
       grind)
    | exact resolve eq425333 eq89117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89117 eq425333
  have eq566079 : (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq566074
  have eq566092 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | (have r₁ := eq566079
       have r₂ := eq451164
       grind)
    | exact resolve eq566079 eq451164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451164 eq566079
  have eq567404 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ x)) := by
    first
    | exact superpose eq566092 eq400232
    | exact resolve eq400232 eq566092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400232 eq566092
  have eq567533 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (τ (σ x)) := by grind
  clear eq567404
  have eq567576 : (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq567533
       have r₂ := eq392782
       grind)
    | exact resolve eq567533 eq392782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392782 eq567533
  have eq568711 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq567576 eq11
    | exact resolve eq11 eq567576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567576
  have eq568754 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq21 eq568711
    | exact resolve eq568711 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq568711
  have eq568755 : (σ (M.op x y)) = (σ x) := by grind
  clear eq568754
  have eq568772 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq568755 eq31
    | exact resolve eq31 eq568755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq572329 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq568755 eq173946
    | exact resolve eq173946 eq568755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173946
  have eq582293 : (σ x) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq568755 eq343839
    | exact resolve eq343839 eq568755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343839 eq568755
  have eq583192 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq582293
       have i₂ := eq181311 sF2
       grind)
    | exact superpose eq181311 eq582293
    | exact resolve eq582293 eq181311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181311 eq582293
  have eq583193 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq583192
  have eq586118 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq89119 (σ x) (σ y)
       grind)
    | (have r₁ := eq572329
       have r₂ := eq89119 (σ x) (σ y)
       grind)
    | exact resolve eq572329 eq89119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89119 eq572329
  have eq597874 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq586118
       have r₂ := eq568772
       grind)
    | exact resolve eq586118 eq568772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586118
  have eq604606 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq583193 eq597874
    | exact resolve eq597874 eq583193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597874
  have eq609147 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq604606
       have r₂ := eq568772
       grind)
    | exact resolve eq604606 eq568772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604606
  have eq617719 : (σ y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq609147 eq97803
    | exact resolve eq97803 eq609147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97803 eq609147
  have eq618077 : (σ x) = (σ y) := by
    first
    | exact superpose eq583193 eq617719
    | exact resolve eq617719 eq583193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617719
  have eq624017 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq618077 eq568772
    | exact resolve eq568772 eq618077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568772 eq618077
  have eq627021 : (σ x) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq624017
       have i₂ := eq88860 sF2
       grind)
    | exact superpose eq88860 eq624017
    | exact resolve eq624017 eq88860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88860 eq624017
  have eq629730 : False := by grind
  exact eq629730

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyy_pxy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) X2) X0
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq285 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq286 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq285 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq285 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq285 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq297 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq286 (σ X0)
       grind)
    | exact superpose eq286 eq15
    | exact resolve eq15 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq286 (τ X0)
       grind)
    | exact superpose eq286 eq17
    | exact resolve eq17 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq309 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq304 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq304
    | exact resolve eq304 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304
  have eq316 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq297 X0
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq297
    | exact resolve eq297 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq329 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq309 X0
       have i₂ := eq286 X0
       grind)
    | exact superpose eq286 eq309
    | exact resolve eq309 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286 eq309
  have eq354 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X1
       have i₂ := eq316 X0
       grind)
    | exact superpose eq316 eq61
    | exact resolve eq61 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq398 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq329 X0
       grind)
    | exact superpose eq329 eq10
    | exact resolve eq10 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq1021 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq362 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq362 X0 X1
       grind)
    | exact superpose eq362 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq362 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq362 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq362 X0 X1
       grind)
    | exact resolve eq13 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq1028 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1021 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1029 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1028 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1034 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1029 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1029
    | (have j0 := eq1029 X0 X1
       grind)
    | exact resolve eq1029 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1035 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1034 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1058 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1035 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1035
    | (have j0 := eq1035 (τ X1) (τ X0)
       grind)
    | exact resolve eq1035 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1105 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1058 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1058
    | (have j0 := eq1058 X0 X1
       grind)
    | exact resolve eq1058 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1122 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1105 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1105
    | (have j0 := eq1105 X0 X1
       grind)
    | exact resolve eq1105 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq1127 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1122
    | (have j0 := eq1122 X0 X1
       grind)
    | exact resolve eq1122 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1132 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1127 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1127
    | (have j0 := eq1127 X0 X1
       grind)
    | exact resolve eq1127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1137 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1132 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1132
    | (have j0 := eq1132 X0 X1
       grind)
    | exact resolve eq1132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1139 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1137 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1137
    | (have j0 := eq1137 (τ X0) (τ X1)
       grind)
    | exact resolve eq1137 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1144 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1035 X0 X1
       have i₂ := eq1137 X1 X0
       grind)
    | exact superpose eq1137 eq1035
    | (have j0 := eq1035 X0 X1
       have j1 := eq1137 (σ X1) (σ X0)
       grind)
    | exact resolve eq1035 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035
  have eq1145 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1137 X1 (σ X0)
       grind)
    | exact superpose eq1137 eq22
    | (have j1 := eq1137 X1 (σ X0)
       grind)
    | exact resolve eq22 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1312 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1145 (M.op X0 X0) (M.op (σ X0) X1)
       have i₂ := eq354 X0 X1
       grind)
    | exact superpose eq354 eq1145
    | exact resolve eq1145 eq354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq1145
  have eq1375 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) (M.op X0 X0)) = X0 ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1312 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1312
    | (have j0 := eq1312 X0 X1
       grind)
    | exact resolve eq1312 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1312
  have eq1727 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1139 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1787 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1727 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1727
    | (have j0 := eq1727 (σ X1) (σ X0)
       grind)
    | exact resolve eq1727 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1797 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1787 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1787
    | (have j0 := eq1787 X0 X1
       grind)
    | exact resolve eq1787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787
  have eq1800 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1797 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1797
    | (have j0 := eq1797 X0 X1
       grind)
    | exact resolve eq1797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1797
  have eq1801 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1800 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1800
    | (have j0 := eq1800 X0 X1
       grind)
    | exact resolve eq1800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1802 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1801 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1801
    | (have j0 := eq1801 X0 X1
       grind)
    | exact resolve eq1801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq1805 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1802 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1802
    | (have j0 := eq1802 (σ X0) (σ X1)
       grind)
    | exact resolve eq1802 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq2534 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op (σ (τ X0)) X1)) (τ (M.op X0 X0))) ∨ (σ (τ X0)) = (σ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1375 (τ X0) X1
       have i₂ := eq398 X0
       grind)
    | exact superpose eq398 eq1375
    | exact resolve eq1375 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq1375
  have eq2552 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op (σ (τ X0)) X1) (M.op X0 X0))) ∨ (σ (τ X0)) = (σ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2534 X0 X1
       have i₂ := eq31 (M.op X0 X0) (M.op (σ (τ X0)) X1)
       grind)
    | exact superpose eq31 eq2534
    | (have j0 := eq2534 X0 X1
       grind)
    | exact resolve eq2534 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2534
  have eq2562 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) ∨ (σ (τ X0)) = (σ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2552 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2552
    | (have j0 := eq2552 X0 X1
       grind)
    | exact resolve eq2552 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq2571 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X0 X0) ∨ (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2562 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq2562
    | (have j0 := eq2562 X0 X1
       grind)
    | exact resolve eq2562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562
  have eq2577 : ∀ X0 X1 : G, (τ X0) = (τ (k (M.op X0 X1) (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2571 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2571
    | (have j0 := eq2571 X0 X1
       grind)
    | exact resolve eq2571 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq2622 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op X0 X1) (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k (M.op X0 X1) (M.op X0 X0))
       have i₂ := eq2577 X0 X1
       grind)
    | exact superpose eq2577 eq11
    | (have j1 := eq2577 X0 X1
       grind)
    | exact resolve eq11 eq2577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq2677 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2622 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2622
    | (have j0 := eq2622 X0 X1
       grind)
    | exact resolve eq2622 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2622
  have eq2779 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2677 (M.op x x) X1
       have i₂ := eq61 x x x
       grind)
    | exact superpose eq61 eq2677
    | (have j0 := eq2677 X0 X1
       grind)
    | exact resolve eq2677 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2677
  have eq2795 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq2779 X0 X1
       have j1 := eq79 X0 X0 X1
       grind)
    | (have r₁ := eq2779 X1 X1
       have r₂ := eq79 X1 X1 x
       grind)
    | exact resolve eq2779 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq2779
  have eq2852 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2795 (M.op x x) X1
       have i₂ := eq61 x x x
       grind)
    | exact superpose eq61 eq2795
    | exact resolve eq2795 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2795
  have eq2902 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2852 (M.op X1 X0) (M.op X0 x)
       have i₂ := eq61 X1 X0 x
       grind)
    | exact superpose eq61 eq2852
    | exact resolve eq2852 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq127353 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1144 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq127407 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127353 x y
       grind)
    | exact superpose eq127353 eq16
    | (have j1 := eq127353 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq127353 x y
       grind)
    | exact resolve eq16 eq127353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127353
  have eq127643 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq127407
  have eq127941 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq127643
       grind)
    | exact superpose eq127643 eq16
    | exact resolve eq16 eq127643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127952 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq127643
       grind)
    | exact superpose eq127643 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq127643
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq127643
       grind)
    | exact resolve eq12 eq127643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127953 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq127643
       grind)
    | exact superpose eq127643 eq61
    | exact resolve eq61 eq127643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127643
  have eq127975 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq127952
  have eq127983 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127975
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq127975
    | exact resolve eq127975 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127975
  have eq127994 : (σ (M.op x x)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127983
       have i₂ := eq316 x
       grind)
    | exact superpose eq316 eq127983
    | exact resolve eq127983 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127983
  have eq127998 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1137 eq127994
    | (have j1 := eq1137 y x
       grind)
    | exact resolve eq127994 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq127994
  have eq128117 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127941
       have i₂ := eq127998
       grind)
    | exact superpose eq127998 eq127941
    | exact resolve eq127941 eq127998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127941
  have eq128119 : (M.op x y) = (τ (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq127998
       grind)
    | exact superpose eq127998 eq10
    | exact resolve eq10 eq127998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127998
  have eq128287 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by grind
  clear eq128117
  have eq128365 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128119
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq128119
    | exact resolve eq128119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128119
  have eq128381 : (M.op x x) = (k y (M.op (M.op x x) (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2902 y x
       have i₂ := eq128365
       grind)
    | exact superpose eq128365 eq2902
    | exact resolve eq2902 eq128365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902 eq128365
  have eq128395 : (k y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128381
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq128381
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq128381
    | exact resolve eq128381 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128381
  have eq128401 : (k y x) = (M.op x x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq128395
       have r₂ := eq12 y x
       grind)
    | exact resolve eq128395 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128395
  have eq128909 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq127953 (M.op x (σ x))
       have i₂ := eq127953 x
       grind)
    | exact superpose eq127953 eq127953
    | exact resolve eq127953 eq127953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127953
  have eq128951 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq128909
  have eq128960 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128951
       have i₂ := eq316 x
       grind)
    | exact superpose eq316 eq128951
    | exact resolve eq128951 eq316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq128951
  have eq128966 : x = (M.op x y) := by
    first
    | (have r₁ := eq128960
       have r₂ := eq128287
       grind)
    | exact resolve eq128960 eq128287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128287 eq128960
  have eq128969 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq128966
       grind)
    | exact superpose eq128966 eq16
    | exact resolve eq16 eq128966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128971 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 x y
       have i₂ := eq128966
       grind)
    | exact superpose eq128966 eq61
    | exact resolve eq61 eq128966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq128966
  have eq128995 : x = (M.op x x) := by
    first
    | (have i₁ := eq128971 (M.op x x)
       have i₂ := eq128971 x
       grind)
    | exact superpose eq128971 eq128971
    | exact resolve eq128971 eq128971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128971
  have eq129030 : x = (k y x) := by
    first
    | (have i₁ := eq128401
       have i₂ := eq128995
       grind)
    | exact superpose eq128995 eq128401
    | exact resolve eq128401 eq128995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128401 eq128995
  have eq129244 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1805 y x
       have i₂ := eq129030
       grind)
    | exact superpose eq129030 eq1805
    | (have j0 := eq1805 y x
       grind)
    | exact resolve eq1805 eq129030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805 eq129030
  have eq129284 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq129244
  have eq129305 : False := by grind
  exact eq129305
