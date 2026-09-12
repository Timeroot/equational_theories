import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation842`: `x = x ◇ ((y ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation842 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law842 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law842.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1004 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq1005 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1040 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1005
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1005
    | exact resolve eq1005 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005
  have eq1041 : (M.op x y) = (k y y) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq1004
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1004
    | exact resolve eq1004 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1068 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16676 : (M.op x y) ≠ (k y y) ∨ x = y ∨ (k x y) = (k y y) := by
    first
    | (have i₁ := eq1068 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1068
    | (have j0 := eq1068 y x
       grind)
    | exact resolve eq1068 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16677 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1068
    | (have j0 := eq1068 (σ y) (σ x)
       grind)
    | exact resolve eq1068 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq16695 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq16676
       have i₂ := eq1041
       grind)
    | exact superpose eq1041 eq16676
    | (have r₁ := eq16676
       have r₂ := eq1041
       grind)
    | exact resolve eq16676 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq16676
  have eq16696 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k x y) := by grind
  clear eq16695
  have eq16697 : (M.op x y) = (k x y) ∨ x = y := by grind
  clear eq16696
  have eq16703 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq16697
       grind)
    | exact superpose eq16697 eq40
    | exact resolve eq40 eq16697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq16697
  have eq16705 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq16703
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16703
    | exact resolve eq16703 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16703
  have eq16709 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq16705
    | exact resolve eq16705 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16705
  have eq16841 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1040 eq16677
    | (have r₁ := eq16677
       have r₂ := eq1040
       grind)
    | exact resolve eq16677 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq16677
  have eq16842 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq16841
  have eq16843 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq16842
  have eq16850 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16843 eq16709
    | exact resolve eq16709 eq16843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16709 eq16843
  have eq16855 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16850
       have r₂ := eq27
       grind)
    | exact resolve eq16850 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16850
  have eq16863 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq16855 eq31
    | exact resolve eq31 eq16855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq16855
  have eq16964 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq16863
    | exact resolve eq16863 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16863
  have eq16965 : x = y := by grind
  clear eq16964
  have eq16970 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16965
       grind)
    | exact superpose eq16965 eq18
    | exact resolve eq18 eq16965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq16971 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq16965
       grind)
    | exact superpose eq16965 eq24
    | exact resolve eq24 eq16965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16965
  have eq17007 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16971
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16971
    | exact resolve eq16971 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16971
  have eq17008 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq16970
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq16970
    | exact resolve eq16970 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16970
  have eq17009 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq17007 eq26
    | exact resolve eq26 eq17007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq17007
  have eq17107 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17009
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq17009
    | exact resolve eq17009 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq17009
  have eq17111 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq17008
       grind)
    | exact superpose eq17008 eq39
    | exact resolve eq39 eq17008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq17008
  have eq17140 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq17111
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17111
    | exact resolve eq17111 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17111
  have eq17146 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17107 eq17140
    | exact resolve eq17140 eq17107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17107 eq17140
  have eq17151 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq17146
    | exact resolve eq17146 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq17146
  have eq17153 : False := by grind
  exact eq17153

/-- `Equation882`: `x = y ◇ ((x ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation882 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law882 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law882.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq80 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq94 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq88
  have eq250 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq94 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq94 X0 X1
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq94 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq94 X0 X1
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq268 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq272 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq268 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq282 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq272 X0 X1
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq272 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq272
  have eq289 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq282
    | (have j0 := eq282 X0 X1
       grind)
    | exact resolve eq282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq290 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq294 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq290
    | exact resolve eq290 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq290 x y
       grind)
    | exact superpose eq290 eq16
    | exact resolve eq16 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq419 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq294 X0 (τ X1)
       grind)
    | exact superpose eq294 eq17
    | exact resolve eq17 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq294
  have eq442 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq419
    | exact resolve eq419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq453 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq442 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq442
    | exact resolve eq442 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq442
  have eq477 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq306
       have i₂ := eq453 x y
       grind)
    | exact superpose eq453 eq306
    | exact resolve eq306 eq453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq453
  have eq478 : False := by grind
  exact eq478

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyx_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq32 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (M.op (M.op X1 X0) (M.op X1 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 X0
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (M.op X1 (M.op X0 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | (have r₁ := eq32 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 (M.op X0 X0))
       have r₂ := eq19 X0 X1
       grind)
    | (have r₁ := eq32 (M.op X1 (M.op X0 X0)) (M.op (M.op X1 X0) (M.op X1 X0))
       have r₂ := eq19 X0 X1
       grind)
    | exact resolve eq32 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op (M.op X1 X0) (M.op X1 X0)) X1) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (k (M.op (M.op X1 X0) (M.op X1 X0)) X1) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq56 : ∀ X0 X1 : G, (k (M.op (M.op X1 X0) (M.op X1 X0)) X1) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0))) ∨ (M.op X1 (M.op X0 X0)) ≠ X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq19 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 X0 X1
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq57 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (k (M.op X1 (M.op X0 X0)) X1) = (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq68 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq75 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq19 (M.op X1 X1) X0
       grind)
    | exact superpose eq19 eq86
    | exact resolve eq86 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq19 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq19 X1 X1
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq97 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq98 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq96 X1 X0
       grind)
    | exact superpose eq96 eq97
    | exact resolve eq97 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq103 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq71
    | exact resolve eq71 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X2 (M.op X0 X1)
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X1 (σ X0)
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq87
    | (have j1 := eq71 X0 X0
       grind)
    | exact resolve eq87 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq118 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq87 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq87 (M.op X0 X0) X0
       grind)
    | exact superpose eq87 eq87
    | exact resolve eq87 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 (M.op X1 (σ (k X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq138 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op (M.op X1 (M.op X1 X0)) X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq57
    | (have j0 := eq57 (k X0 X1) (M.op (M.op X1 (M.op X1 X0)) X0)
       grind)
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq157 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 (M.op X0 X0) X1
       have i₂ := eq87 (M.op X0 X0) X0
       grind)
    | exact superpose eq87 eq98
    | exact resolve eq98 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq157
    | exact resolve eq157 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq199 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173 X1 X2
       have i₂ := eq173 X1 X0
       grind)
    | (have i₁ := eq173 X0 X1
       have i₂ := eq173 X0 X0
       grind)
    | exact superpose eq173 eq173
    | exact resolve eq173 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X1 X2
       have i₂ := eq173 X1 X0
       grind)
    | (have i₁ := eq98 X0 X1
       have i₂ := eq173 X0 X0
       grind)
    | exact superpose eq173 eq98
    | exact resolve eq98 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq205 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1
       have i₂ := eq173 X1 X0
       grind)
    | (have i₁ := eq68 X0
       have i₂ := eq173 X0 X0
       grind)
    | exact superpose eq173 eq68
    | exact resolve eq68 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq208 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq87 X1 X1
       have i₂ := eq173 X1 X0
       grind)
    | (have i₁ := eq87 X0 X0
       have i₂ := eq173 X0 X0
       grind)
    | exact superpose eq173 eq87
    | exact resolve eq87 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq243 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 (M.op X1 (σ X0)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X1 (M.op X1 (σ X0))) X0
       have i₂ := eq205 X1 (σ X0)
       grind)
    | exact superpose eq205 eq23
    | exact resolve eq23 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (k (τ (M.op X1 (M.op X1 (σ X0)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq243 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq243
    | exact resolve eq243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq663 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) = (M.op X1 (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq116 (M.op (M.op X0 X0) (M.op X0 X0)) X0 X1
       have i₂ := eq118 (M.op X0 X0)
       grind)
    | exact superpose eq118 eq116
    | exact resolve eq116 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq710 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq663 X0 x
       have i₂ := eq87 x (M.op X0 X0)
       grind)
    | exact superpose eq87 eq663
    | exact resolve eq663 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq717 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq710 X0
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq710
    | exact resolve eq710 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq728 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq717 X1
       have i₂ := eq199 X1 X1 X0
       grind)
    | (have i₁ := eq717 X1
       have i₂ := eq199 X0 X1 X1
       grind)
    | exact superpose eq199 eq717
    | exact resolve eq717 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq795 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X1 X1
       have i₂ := eq199 X1 X1 x
       grind)
    | (have i₁ := eq96 X1 X1
       have i₂ := eq199 X0 X1 X1
       grind)
    | exact superpose eq199 eq96
    | exact resolve eq96 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq832 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq795 X0 X1
       have i₂ := eq208 X0 X1
       grind)
    | exact superpose eq208 eq795
    | exact resolve eq795 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq931 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X1))
       have i₂ := eq728 X0 X1
       grind)
    | exact superpose eq728 eq9
    | exact resolve eq9 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq939 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X2 (M.op X2 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq199 X1 X0 (M.op X2 (M.op X2 X0))
       have i₂ := eq728 X2 X0
       grind)
    | exact superpose eq728 eq199
    | exact resolve eq199 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq963 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq931 X0 X1
       have i₂ := eq19 X0 X0
       grind)
    | exact superpose eq19 eq931
    | exact resolve eq931 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq1187 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq204 X1 X2 X1
       have i₂ := eq199 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq204 X1 X2 X1
       have i₂ := eq199 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq199 eq204
    | exact resolve eq204 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1418 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X0 (M.op X1 (M.op X1 (M.op X0 X2)))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq87 X3 X2
       have i₂ := eq1187 X1 X0 X2
       grind)
    | exact superpose eq1187 eq87
    | exact resolve eq87 eq1187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1820 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq963 X1 X2
       have i₂ := eq199 X1 X1 X0
       grind)
    | (have i₁ := eq963 X1 X2
       have i₂ := eq199 X0 X1 X1
       grind)
    | exact superpose eq199 eq963
    | exact resolve eq963 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq963
  have eq2099 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) ≠ X0 ∨ (k (M.op X2 (M.op X2 X0)) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X2 X1))
       have i₂ := eq1820 X0 X1 X2
       grind)
    | exact superpose eq1820 eq12
    | exact resolve eq12 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2104 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) ≠ X0 ∨ (k (M.op X2 (M.op X2 X0)) (M.op X1 (M.op X1 X0))) = (M.op (M.op (M.op X1 (M.op X1 X0)) X0) (M.op X2 (M.op X2 X0))) ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq138 (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X2 X1))
       have i₂ := eq1820 X0 X1 X2
       grind)
    | exact superpose eq1820 eq138
    | exact resolve eq138 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq2122 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X2 X0))) = (k (M.op X2 (M.op X2 X0)) (M.op X1 (M.op X1 X0))) ∨ (M.op X2 (M.op X2 X0)) ≠ X0 ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2104 X0 X1 X2
       have i₂ := eq728 X1 X0
       grind)
    | exact superpose eq728 eq2104
    | (have j0 := eq2104 X0 X1 X2
       grind)
    | exact resolve eq2104 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq2104
  have eq2178 : ∀ X0 X1 X2 : G, (k (M.op X2 (M.op X2 X0)) (M.op X1 (M.op X1 X0))) = X0 ∨ (M.op X2 (M.op X2 X0)) ≠ X0 ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2122 X0 X1 X2
       have i₂ := eq832 X2 X0
       grind)
    | exact superpose eq832 eq2122
    | (have j0 := eq2122 X0 X1 X2
       grind)
    | exact resolve eq2122 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq2122
  have eq2192 : ∀ X0 X1 X2 : G, (k (M.op X2 (M.op X2 X0)) (M.op X1 (M.op X1 X0))) = X0 ∨ (M.op X2 (M.op X2 X0)) ≠ X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2178 X0 X1 X2
       have j1 := eq2099 X0 X2 X2
       grind)
    | (have r₁ := eq2178 X0 X1 X2
       have r₂ := eq2099 X0 X1 X2
       grind)
    | exact resolve eq2178 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099 eq2178
  have eq2207 : ∀ X0 X1 : G, (σ X0) = (k (σ (M.op (τ X1) (M.op X0 X0))) X1) ∨ (M.op (τ X1) (M.op X0 X0)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 (M.op (τ X0) (M.op X1 X1))
       have i₂ := eq87 (τ X0) X1
       grind)
    | exact superpose eq87 eq75
    | exact resolve eq75 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq4615 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (k X0 (σ X1)) ∨ (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (k X0 (σ X1)) (σ X2)
       have i₂ := eq103 X0 X1 X2
       grind)
    | exact superpose eq103 eq13
    | (have j0 := eq13 (k X0 (σ X1)) (σ X2)
       have j1 := eq103 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k X0 (σ X1)) (σ X2)
       have r₂ := eq103 X0 X1 X2
       grind)
    | exact resolve eq13 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4639 : ∀ X0 X1 X2 : G, (σ X0) ≠ (k X1 (σ X2)) ∨ (M.op (σ X0) (k X1 (σ X2))) = (σ (k (k (τ X1) X2) X0)) ∨ (σ X0) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq103 X1 X2 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq4641 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (σ X2) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4615 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4615
  have eq4644 : ∀ X0 X1 X2 : G, (k (k X0 (σ X1)) (σ X2)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ X2) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4641 X0 X1 X2
       have j1 := eq4639 X2 X0 X1
       grind)
    | (have r₁ := eq4641 X1 X2 X0
       have r₂ := eq4639 X0 X1 X2
       grind)
    | exact resolve eq4641 eq4639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639 eq4641
  have eq4666 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4644 X0 X1 X2
       have i₂ := eq22 X0 X1 X2
       grind)
    | exact superpose eq22 eq4644
    | (have j0 := eq4644 X0 X1 X2
       grind)
    | exact resolve eq4644 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4644
  have eq12666 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 (M.op X1 (σ (k (τ X0) (τ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq124 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq124
    | exact resolve eq124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq12805 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k (σ (τ X0)) X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12666 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq12666
    | (have j0 := eq12666 X0 X1
       grind)
    | exact resolve eq12666 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12666
  have eq12808 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12805 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq12805
    | (have j0 := eq12805 X0 X1
       grind)
    | exact resolve eq12805 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12805
  have eq12884 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 (k X0 X0)) (M.op X1 (k X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X1 (k X0 X0)) X1
       have i₂ := eq12808 X0 X1
       grind)
    | exact superpose eq12808 eq19
    | (have j1 := eq12808 X0 X1
       grind)
    | exact resolve eq19 eq12808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq12808
  have eq12943 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq12884 X0 x
       have i₂ := eq9 (k X0 X0) x
       grind)
    | exact superpose eq9 eq12884
    | (have j0 := eq12884 X0 x
       grind)
    | exact resolve eq12884 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12884
  have eq12961 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12943 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq12943 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq12943 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12943
  have eq12998 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq12961 (σ X0)
       grind)
    | exact superpose eq12961 eq15
    | exact resolve eq15 eq12961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13005 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq12961 (τ X0)
       grind)
    | exact superpose eq12961 eq34
    | exact resolve eq34 eq12961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13020 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13005 X0
       have i₂ := eq12961 X0
       grind)
    | exact superpose eq12961 eq13005
    | exact resolve eq13005 eq12961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13005
  have eq13027 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12998 X0
       have i₂ := eq12961 X0
       grind)
    | exact superpose eq12961 eq12998
    | exact resolve eq12998 eq12961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12998
  have eq13219 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X1 (τ X0)
       have i₂ := eq13020 X0
       grind)
    | exact superpose eq13020 eq87
    | exact resolve eq87 eq13020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq13020
  have eq13377 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq118 (σ X0)
       have i₂ := eq13027 X0
       grind)
    | exact superpose eq13027 eq118
    | exact resolve eq118 eq13027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq13549 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (τ X0))) = (τ (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13219 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq1820 X1 X0 X1
       grind)
    | exact superpose eq1820 eq13219
    | exact resolve eq13219 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13219
  have eq15424 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq13377 (M.op X0 (M.op X0 X1))
       have i₂ := eq1820 X0 X1 X0
       grind)
    | exact superpose eq1820 eq13377
    | exact resolve eq13377 eq1820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820 eq13377
  have eq16838 : ∀ X0 X1 : G, (M.op X0 (σ (M.op X1 (M.op X1 (τ X0))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15424 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15424
    | exact resolve eq15424 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15424
  have eq17195 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op X2 X0))))) = (σ (M.op X3 (M.op X3 (τ X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1418 X0 X2 (σ (M.op X3 (M.op X3 (τ X0)))) X1
       have i₂ := eq16838 X0 X3
       grind)
    | exact superpose eq16838 eq1418
    | exact resolve eq1418 eq16838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418 eq16838
  have eq17211 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X0)) = (σ (M.op X3 (M.op X3 (τ X0)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq17195 X0 X1 x X3
       have i₂ := eq208 x X0
       grind)
    | exact superpose eq208 eq17195
    | exact resolve eq17195 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq17195
  have eq38535 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ (M.op (τ (σ X1)) (M.op X0 X0)))) X1) ∨ (M.op (τ (σ X1)) (M.op X0 X0)) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ (M.op (τ (σ X1)) (M.op X0 X0))) X1
       have i₂ := eq2207 X0 (σ X1)
       grind)
    | exact superpose eq2207 eq23
    | (have j1 := eq2207 X0 (σ X1)
       grind)
    | exact resolve eq23 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2207
  have eq38567 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (τ (σ X1)) (M.op X0 X0)) X1) ∨ (M.op (τ (σ X1)) (M.op X0 X0)) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38535 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) (M.op X0 X0))
       grind)
    | exact superpose eq10 eq38535
    | (have j0 := eq38535 X0 X1
       grind)
    | exact resolve eq38535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38535
  have eq38604 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op X1 (M.op X0 X0)) X1) ∨ (M.op (τ (σ X1)) (M.op X0 X0)) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38567 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq38567
    | (have j0 := eq38567 X0 X1
       grind)
    | exact resolve eq38567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38567
  have eq38630 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 X0)) X1) = X0 ∨ (M.op (τ (σ X1)) (M.op X0 X0)) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38604 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38604
    | (have j0 := eq38604 X0 X1
       grind)
    | exact resolve eq38604 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38604
  have eq38650 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (k (M.op X1 (M.op X0 X0)) X1) = X0 ∨ (τ (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38630 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq38630
    | (have j0 := eq38630 X0 X1
       grind)
    | exact resolve eq38630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38630
  have eq38661 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 (M.op X0 X0)) = X0 ∨ (k (M.op X1 (M.op X0 X0)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38650 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq38650
    | (have j0 := eq38650 X0 X1
       grind)
    | exact resolve eq38650 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38650
  have eq38667 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 X0)) X1) = X0 ∨ (M.op X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38661 X0 X1
       have j1 := eq33 X0 X1
       grind)
    | (have r₁ := eq38661 X0 X1
       have r₂ := eq33 X0 X1
       grind)
    | (have r₁ := eq38661 X1 X0
       have r₂ := eq33 X0 X1
       grind)
    | (have r₁ := eq38661 X1 X1
       have r₂ := eq33 (M.op X1 (M.op X1 X1)) X1
       grind)
    | exact resolve eq38661 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38661
  have eq180173 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38667 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq38667
    | exact resolve eq38667 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180221 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X2 X1))) = X1 ∨ (M.op X0 (M.op X0 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq38667 X0 (M.op X2 (M.op X2 X0))
       have i₂ := eq939 X0 X1 X2
       grind)
    | exact superpose eq939 eq38667
    | exact resolve eq38667 eq939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939 eq38667
  have eq180367 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X0 X1)) (M.op X2 (M.op X2 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq180221 X0 X1 X2
       have j1 := eq2192 X1 X2 X0
       grind)
    | (have r₁ := eq180221 X2 X0 X2
       have r₂ := eq2192 X0 X1 X2
       grind)
    | exact resolve eq180221 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192 eq180221
  have eq181130 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq180173 X1 (τ X0)
       grind)
    | exact superpose eq180173 eq18
    | (have j1 := eq180173 X1 (τ X0)
       grind)
    | exact resolve eq18 eq180173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq181213 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq180173 (σ X1) (σ X0)
       grind)
    | exact superpose eq180173 eq15
    | (have j1 := eq180173 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq180173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180173
  have eq181623 : ∀ X0 X1 X3 : G, (τ X1) = (k (τ (M.op X0 (M.op X0 X1))) (M.op X3 (M.op X3 (τ X1)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq180367 x (τ X1) X3
       have i₂ := eq13549 X1 X0 x
       grind)
    | exact superpose eq13549 eq180367
    | exact resolve eq180367 eq13549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13549
  have eq181826 : ∀ X0 X1 X2 : G, (k (M.op X2 (M.op X2 X1)) (σ (M.op X0 (M.op X0 (τ X1))))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180367 X2 X1 x
       have i₂ := eq17211 X1 x X0
       grind)
    | exact superpose eq17211 eq180367
    | exact resolve eq180367 eq17211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17211 eq180367
  have eq230534 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq181130 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq181130
    | exact resolve eq181130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181130
  have eq231147 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq230534 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq230534
    | (have j0 := eq230534 X0 X1
       grind)
    | exact resolve eq230534 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230534
  have eq267427 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (k (k (τ (M.op X2 (M.op X2 X0))) (M.op X3 (M.op X3 (τ X0)))) X1)) ∨ (M.op X0 X0) = (σ (k (k (τ (M.op X2 (M.op X2 X0))) (M.op X3 (M.op X3 (τ X0)))) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4666 (M.op X2 (M.op X2 X1)) (M.op X0 (M.op X0 (τ X1))) X2
       have i₂ := eq181826 X0 X1 X2
       grind)
    | exact superpose eq181826 eq4666
    | exact resolve eq4666 eq181826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4666 eq181826
  have eq267758 : ∀ X0 X1 X2 X3 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k (k (τ (M.op X2 (M.op X2 X0))) (M.op X3 (M.op X3 (τ X0)))) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq267427 X0 X1 X2 X3
       have i₂ := eq181623 X2 X0 X3
       grind)
    | exact superpose eq181623 eq267427
    | (have j0 := eq267427 X0 X1 X2 X3
       grind)
    | exact resolve eq267427 eq181623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267427
  have eq267927 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k (k (τ (M.op X2 (M.op X2 X0))) (M.op X3 (M.op X3 (τ X0)))) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq267758 X0 X1 X2 X3
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq267758
    | (have j0 := eq267758 X0 X1 X2 X3
       grind)
    | exact resolve eq267758 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267758
  have eq268038 : ∀ X0 X1 X2 X3 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (k (k (τ (M.op X2 (M.op X2 X0))) (M.op X3 (M.op X3 (τ X0)))) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq267927 X0 X1 X2 X3
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq267927 X0 X1 X2 X3
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq267927 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267927
  have eq268124 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq268038 X0 X1 x x
       have i₂ := eq181623 x X0 x
       grind)
    | exact superpose eq181623 eq268038
    | (have j0 := eq268038 X0 X1 x x
       grind)
    | exact resolve eq268038 eq181623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181623 eq268038
  have eq268174 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq268124 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq268124
    | (have j0 := eq268124 X0 X1
       grind)
    | exact resolve eq268124 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq268124
  have eq2446562 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq268174 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq268174
    | exact resolve eq268174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268174
  have eq2448997 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2446562 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446562
  have eq2706078 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181213 x y
       grind)
    | exact superpose eq181213 eq16
    | (have j1 := eq181213 x y
       grind)
    | exact resolve eq16 eq181213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2707240 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq181213 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181213
  have eq2709150 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2707240 (τ X1) (τ X0)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq2707240
    | (have j0 := eq2707240 (τ X1) (τ X0)
       grind)
    | exact resolve eq2707240 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq2709382 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2709150 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq2709150
    | (have j0 := eq2709150 X0 X1
       grind)
    | exact resolve eq2709150 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709150
  have eq2709662 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2709382 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2709382
    | (have j0 := eq2709382 X0 X1
       grind)
    | exact resolve eq2709382 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709382
  have eq2709792 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2709662 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2709662
    | (have j0 := eq2709662 X0 X1
       grind)
    | exact resolve eq2709662 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709662
  have eq2709878 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2709792 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2709792
    | (have j0 := eq2709792 X0 X1
       grind)
    | exact resolve eq2709792 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709792
  have eq2725400 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2706078
       have i₂ := eq231147 x y
       grind)
    | exact superpose eq231147 eq2706078
    | (have j1 := eq231147 (σ x) (σ y)
       grind)
    | (have r₁ := eq2706078
       have r₂ := eq231147 x y
       grind)
    | exact resolve eq2706078 eq231147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2706078
  have eq2725403 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2725400
  have eq2725425 : y = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq205 x y
       have i₂ := eq2725403
       grind)
    | exact superpose eq2725403 eq205
    | exact resolve eq205 eq2725403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq2729736 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2725425
       have i₂ := eq2725403
       grind)
    | exact superpose eq2725403 eq2725425
    | exact resolve eq2725425 eq2725403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725425
  have eq2729808 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2729736
  have eq2729812 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2729808
       have i₂ := eq12961 y
       grind)
    | exact superpose eq12961 eq2729808
    | exact resolve eq2729808 eq12961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12961 eq2729808
  have eq2729817 : y = (k (τ (M.op (σ x) (σ y))) y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq248 y (σ x)
       have i₂ := eq2729812
       grind)
    | exact superpose eq2729812 eq248
    | exact resolve eq248 eq2729812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq2746284 : y = (k (τ (σ y)) y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2729817
       have i₂ := eq2729812
       grind)
    | exact superpose eq2729812 eq2729817
    | exact resolve eq2729817 eq2729812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2729812 eq2729817
  have eq2746428 : y = (k (τ (σ y)) y) ∨ y = (M.op y y) := by grind
  clear eq2746284
  have eq2746456 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2746428
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2746428
    | exact resolve eq2746428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746428
  have eq2746482 : y = (M.op y y) := by
    first
    | (have j1 := eq2709878 y y
       grind)
    | (have r₁ := eq2746456
       have r₂ := eq2709878 y y
       grind)
    | exact resolve eq2746456 eq2709878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709878 eq2746456
  have eq2746750 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq2448997 y x
       have i₂ := eq2746482
       grind)
    | exact superpose eq2746482 eq2448997
    | exact resolve eq2448997 eq2746482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448997
  have eq2767954 : y ≠ y ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2746750 x
       have i₂ := eq2725403
       grind)
    | exact superpose eq2725403 eq2746750
    | (have j0 := eq2746750 x
       grind)
    | (have r₁ := eq2746750 x
       have r₂ := eq2725403
       grind)
    | exact resolve eq2746750 eq2725403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725403 eq2746750
  have eq2767992 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2767954
  have eq2826223 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2707240 x y
       have i₂ := eq2767992
       grind)
    | exact superpose eq2767992 eq2707240
    | (have j0 := eq2707240 x y
       grind)
    | exact resolve eq2707240 eq2767992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707240 eq2767992
  have eq2826228 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2826223
  have eq2826229 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2826228
  have eq2830795 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2826229
       grind)
    | exact superpose eq2826229 eq16
    | exact resolve eq16 eq2826229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2830919 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2826229
       grind)
    | exact superpose eq2826229 eq12
    | exact resolve eq12 eq2826229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2830920 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2826229
       grind)
    | exact superpose eq2826229 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2826229
       grind)
    | exact resolve eq13 eq2826229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826229
  have eq2831268 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq2830920
  have eq2831614 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2831268
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2831268
    | exact resolve eq2831268 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831268
  have eq2831615 : (σ y) = (σ (k y x)) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq2830919
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2830919
    | exact resolve eq2830919 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2830919
  have eq2832022 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2831614
       have i₂ := eq13027 y
       grind)
    | exact superpose eq13027 eq2831614
    | exact resolve eq2831614 eq13027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13027 eq2831614
  have eq2832394 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2832022
       have i₂ := eq2746482
       grind)
    | exact superpose eq2746482 eq2832022
    | exact resolve eq2832022 eq2746482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2746482 eq2832022
  have eq2832652 : (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq2832394
       have r₂ := eq2831615
       grind)
    | exact resolve eq2832394 eq2831615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831615 eq2832394
  have eq2837556 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq231147 x y
       have i₂ := eq2832652
       grind)
    | exact superpose eq2832652 eq231147
    | (have j0 := eq231147 x y
       grind)
    | exact resolve eq231147 eq2832652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231147 eq2832652
  have eq2838435 : y = (M.op x y) := by
    first
    | (have r₁ := eq2837556
       have r₂ := eq2830795
       grind)
    | exact resolve eq2837556 eq2830795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837556
  have eq2843504 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2830795
       have i₂ := eq2838435
       grind)
    | exact superpose eq2838435 eq2830795
    | exact resolve eq2830795 eq2838435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2830795 eq2838435
  have eq2843855 : False := by grind
  exact eq2843855

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pyx_pxx_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq41 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq44 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq79 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq61 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq61 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq61 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq138 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq140 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       have j1 := eq79 X0 X1
       grind)
    | (have r₁ := eq138 X0 X1
       have r₂ := eq79 X0 X1
       grind)
    | (have r₁ := eq138 X1 X1
       have r₂ := eq79 X1 X1
       grind)
    | exact resolve eq138 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq138
  have eq512 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq140 (σ X1) (σ X0)
       grind)
    | exact superpose eq140 eq15
    | exact resolve eq15 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq515 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq512 X0 X1
       have i₂ := eq140 X1 X0
       grind)
    | exact superpose eq140 eq512
    | exact resolve eq512 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq512
  have eq520 : False := by grind
  exact eq520

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxy_pyx_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
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
  have eq51 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq70
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq70
    | exact resolve eq70 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq75 : (M.op y y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq74
    | exact resolve eq74 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq83 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq132 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq123 eq16
    | exact resolve eq16 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq159 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (M.op (σ x) (σ X0)) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq282 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq99 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq99
    | (have j0 := eq99 (σ X0)
       grind)
    | exact resolve eq99 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq83
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq83
    | (have j1 := eq99 y
       grind)
    | exact resolve eq83 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq99
  have eq315 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : (M.op y y) = (M.op x (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq321 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (k (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    grind
  have eq329 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq325 X0 X1
       have i₂ := eq53 (M.op X1 X1) X0
       grind)
    | exact superpose eq53 eq325
    | exact resolve eq325 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq331 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq321
       have i₂ := eq53 sF4 sF4
       grind)
    | exact superpose eq53 eq321
    | exact resolve eq321 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq333 : (M.op y y) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq318
       have i₂ := eq53 sF0 sF0
       grind)
    | exact superpose eq53 eq318
    | exact resolve eq318 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq335 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq315 X0 X1
       have i₂ := eq53 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq315
    | exact resolve eq315 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq336 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq329
    | exact resolve eq329 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq340 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq335
    | exact resolve eq335 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq323 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq323 (M.op X0 X0) X0
       grind)
    | exact superpose eq323 eq323
    | exact resolve eq323 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | exact superpose eq331 eq53
    | exact resolve eq53 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq570 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq566
       have i₂ := eq53 (M.op sF4 sF4) sF4
       grind)
    | exact superpose eq53 eq566
    | exact resolve eq566 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq571 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq570
       have i₂ := eq14 sF4 sF4
       grind)
    | exact superpose eq14 eq570
    | exact resolve eq570 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq572 : (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq571
       have i₂ := eq53 sF3 sF3
       grind)
    | exact superpose eq53 eq571
    | exact resolve eq571 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq577 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq572 eq323
    | exact resolve eq323 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | exact superpose eq333 eq53
    | exact resolve eq53 eq333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333
  have eq591 : (M.op (M.op y y) (M.op y y)) = (M.op x (M.op (M.op x y) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq587
       have i₂ := eq53 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq53 eq587
    | exact resolve eq587 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq592 : (M.op x (M.op x y)) = (M.op (M.op y y) (M.op y y)) := by
    first
    | (have i₁ := eq591
       have i₂ := eq14 sF0 sF0
       grind)
    | exact superpose eq14 eq591
    | exact resolve eq591 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq593 : (M.op x (M.op x y)) = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq592
       have i₂ := eq53 y y
       grind)
    | exact superpose eq53 eq592
    | exact resolve eq592 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq654 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq323 y y
       have i₂ := eq593
       grind)
    | exact superpose eq593 eq323
    | exact resolve eq323 eq593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq2709 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq336
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2783 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2709 X0 X1
       have i₂ := eq323 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq323 eq2709
    | exact resolve eq2709 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709
  have eq2942 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) X1
       have i₂ := eq340 X0 X1
       grind)
    | exact superpose eq340 eq53
    | exact resolve eq53 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq2946 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2942 X0 X1
       have i₂ := eq53 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq53 eq2942
    | exact resolve eq2942 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2942
  have eq2986 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2946 X0 X1
       have i₂ := eq53 (M.op X0 X0) X1
       grind)
    | exact superpose eq53 eq2946
    | exact resolve eq2946 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2946
  have eq3019 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2986 X0 X1
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq2986
    | exact resolve eq2986 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2986
  have eq3040 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3019 X0 X1
       have i₂ := eq336 X1 X0
       grind)
    | exact superpose eq336 eq3019
    | exact resolve eq3019 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3019
  have eq3088 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3040 X1 X2
       have i₂ := eq3040 X1 X0
       grind)
    | (have i₁ := eq3040 X0 X1
       have i₂ := eq3040 X0 X0
       grind)
    | exact superpose eq3040 eq3040
    | exact resolve eq3040 eq3040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3091 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op X0 (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq572 eq3040
    | exact resolve eq3040 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq3040
  have eq3835 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq3853 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq282 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq3855 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3835 X0
       have i₂ := eq10 (k X0 X0) X0
       grind)
    | exact superpose eq10 eq3835
    | (have j0 := eq3835 X0
       grind)
    | exact resolve eq3835 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3835
  have eq3962 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq654 eq3088
    | exact resolve eq3088 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3971 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq577 eq3088
    | exact resolve eq3088 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3088
  have eq4585 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (k X0 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq327 X1 (M.op X1 X0)
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq327
    | exact resolve eq327 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq4714 : ∀ X0 X1 : G, (k X0 (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4585 X0 X1
       have i₂ := eq2783 X0 X1
       grind)
    | exact superpose eq2783 eq4585
    | exact resolve eq4585 eq2783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2783 eq4585
  have eq5087 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (k X0 x)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ x))))) ∨ (M.op (σ x) (σ X0)) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq159 eq336
    | (have j1 := eq159 X0
       grind)
    | exact resolve eq336 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq336
  have eq5123 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 (σ y)) (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3091 eq4714
    | exact resolve eq4714 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091
  have eq25879 : y = (M.op y (M.op (M.op y x) (M.op y x))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14 y y
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq14
    | exact resolve eq14 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq25924 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25879
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq25879
    | exact resolve eq25879 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25879
  have eq25960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq25924 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq25924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq25960
    | exact resolve eq25960 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25960
  have eq25972 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq25961
       have r₂ := eq28
       grind)
    | exact resolve eq25961 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25961
  have eq26005 : (σ y) = (M.op (σ y) (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq25972 eq14
    | exact resolve eq14 eq25972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25972
  have eq26050 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq26005
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq26005
    | exact resolve eq26005 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26005
  have eq26095 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq26050 eq342
    | exact resolve eq342 eq26050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26050
  have eq26147 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq26095
    | exact resolve eq26095 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26095
  have eq26173 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq342 y
       have i₂ := eq26147
       grind)
    | exact superpose eq26147 eq342
    | exact resolve eq342 eq26147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26147
  have eq26224 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26173
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26173
    | exact resolve eq26173 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26173
  have eq26243 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26224 eq3971
    | exact resolve eq3971 eq26224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26224
  have eq26247 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26243 x
       have i₂ := eq323 x sF2
       grind)
    | exact superpose eq323 eq26243
    | exact resolve eq26243 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26243
  have eq26745 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq26247
  have eq26806 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq26745
    | exact resolve eq26745 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26745
  have eq27727 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26806 eq25924
    | exact resolve eq25924 eq26806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25924 eq26806
  have eq27733 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq27727
  have eq27737 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq27733
       have r₂ := eq28
       grind)
    | exact resolve eq27733 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27733
  have eq28156 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq342 y
       have i₂ := eq27737
       grind)
    | exact superpose eq27737 eq342
    | exact resolve eq342 eq27737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq27737
  have eq28211 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28156
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28156
    | exact resolve eq28156 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28156
  have eq28212 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq28211
  have eq28221 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28212 eq30
    | exact resolve eq30 eq28212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28212
  have eq28358 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq28221
    | exact resolve eq28221 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28221
  have eq28359 : x = (M.op x y) ∨ x = y := by grind
  clear eq28358
  have eq28432 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x x))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28359 eq3962
    | exact resolve eq3962 eq28359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3962 eq28359
  have eq28436 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq28432 x
       have i₂ := eq323 x x
       grind)
    | exact superpose eq323 eq28432
    | exact resolve eq28432 eq323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq28432
  have eq28942 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq287
       have i₂ := eq28436
       grind)
    | exact superpose eq28436 eq287
    | exact resolve eq287 eq28436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq28952 : (M.op x y) = (k x y) ∨ x = y := by grind
  have eq28973 : x ≠ x ∨ x = y ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq28436
       grind)
    | exact superpose eq28436 eq12
    | exact resolve eq12 eq28436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28436
  have eq28998 : x ≠ x ∨ x = y ∨ x = (k y y) := by grind
  clear eq28973
  have eq28999 : x = (k y y) ∨ x = y := by grind
  clear eq28998
  have eq29000 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq28942
  have eq29015 : (M.op x y) = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq28952
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28952
    | exact resolve eq28952 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28952
  have eq29019 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq29000
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29000
    | exact resolve eq29000 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29000
  have eq29655 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq29015
       grind)
    | exact superpose eq29015 eq45
    | exact resolve eq45 eq29015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29015
  have eq29676 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq29655
    | exact resolve eq29655 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29655
  have eq123318 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3855 y
       have i₂ := eq28999
       grind)
    | exact superpose eq28999 eq3855
    | (have j0 := eq3855 y
       grind)
    | exact resolve eq3855 eq28999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3855 eq28999
  have eq123637 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq123318
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq123318
    | exact resolve eq123318 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq123318
  have eq123672 : (k (σ x) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq123637
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq123637
    | exact resolve eq123637 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123637
  have eq123699 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq123672
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq123672
    | exact resolve eq123672 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123672
  have eq123720 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq123699
    | exact resolve eq123699 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123699
  have eq123733 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq123720
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq123720
    | exact resolve eq123720 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123720
  have eq271586 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq123733 eq29676
    | exact resolve eq29676 eq123733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29676 eq123733
  have eq271627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq271586
  have eq271650 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq271627
       have r₂ := eq28
       grind)
    | exact resolve eq271627 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271627
  have eq271679 : (σ y) = (k (σ y) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ x = y := by
    first
    | exact superpose eq271650 eq5123
    | exact resolve eq5123 eq271650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5123 eq271650
  have eq271786 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq577 eq271679
    | exact resolve eq271679 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq271679
  have eq272978 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq271786 eq29019
    | exact resolve eq29019 eq271786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29019 eq271786
  have eq273039 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq272978
  have eq273590 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq273039 eq30
    | exact resolve eq30 eq273039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq273039
  have eq273950 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq273590
    | exact resolve eq273590 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273590
  have eq273951 : x = y := by grind
  clear eq273950
  have eq273953 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq273951
       grind)
    | exact superpose eq273951 eq25
    | exact resolve eq25 eq273951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq274019 : x = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq654
       have i₂ := eq273951
       grind)
    | exact superpose eq273951 eq654
    | exact resolve eq654 eq273951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq273951
  have eq274278 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq273953
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq273953
    | exact resolve eq273953 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273953
  have eq274279 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq274278 eq27
    | exact resolve eq27 eq274278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq279749 : (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq274019 eq4714
    | exact resolve eq4714 eq274019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4714 eq274019
  have eq279906 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq279749 eq121
    | exact resolve eq121 eq279749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279952 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq21 eq279906
    | exact resolve eq279906 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279906
  have eq282168 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (k X0 x)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ X0)) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq274279 eq5087
    | (have j0 := eq5087 X0
       grind)
    | exact resolve eq5087 eq274279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5087
  have eq282169 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ X0)) ∨ (σ (k X0 x)) = (M.op (σ (k X0 x)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq274279 eq282168
    | (have j0 := eq282168 X0
       grind)
    | exact resolve eq282168 eq274279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282168
  have eq282170 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ (k X0 x)) (M.op (σ X0) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq274279 eq282169
    | (have j0 := eq282169 X0
       grind)
    | exact resolve eq282169 eq274279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282169
  have eq282584 : (σ (k (M.op x y) x)) = (M.op (σ (k (M.op x y) x)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq282170
    | (have j0 := eq282170 (M.op x y)
       grind)
    | exact resolve eq282170 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq282170
  have eq282668 : (σ (k (M.op x y) x)) = (M.op (σ (k (M.op x y) x)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq282584
       have r₂ := eq28
       grind)
    | exact resolve eq282584 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282584
  have eq282916 : (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq121 eq282668
    | exact resolve eq282668 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq282668
  have eq283146 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq279952 eq282916
    | exact resolve eq282916 eq279952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279952 eq282916
  have eq283369 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3971 eq283146
    | exact resolve eq283146 eq3971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3971 eq283146
  have eq283559 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq274278 eq283369
    | exact resolve eq283369 eq274278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283369
  have eq283627 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq274279 eq283559
    | exact resolve eq283559 eq274279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283559
  have eq283671 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq283627
       have r₂ := eq28
       grind)
    | exact resolve eq283627 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283627
  have eq283827 : (σ (M.op x y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq283671 eq14
    | exact resolve eq14 eq283671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283671
  have eq283860 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq52 eq283827
    | exact resolve eq283827 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq283827
  have eq283863 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq274278 eq283860
    | exact resolve eq283860 eq274278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274278 eq283860
  have eq283867 : x = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq283863 eq29
    | exact resolve eq29 eq283863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq283888 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq283863 eq132
    | exact resolve eq132 eq283863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq284144 : (k (M.op x y) x) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq145 eq283888
    | exact resolve eq283888 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq283888
  have eq284165 : x = (M.op x y) := by
    first
    | exact superpose eq31 eq283867
    | exact resolve eq283867 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq283867
  have eq284215 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq279749 eq284144
    | exact resolve eq284144 eq279749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279749 eq284144
  have eq290357 : x = (k x x) := by
    first
    | exact superpose eq284165 eq284215
    | exact resolve eq284215 eq284165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284165 eq284215
  have eq293033 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3853 x
       have i₂ := eq290357
       grind)
    | exact superpose eq290357 eq3853
    | (have j0 := eq3853 x
       grind)
    | exact resolve eq3853 eq290357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3853 eq290357
  have eq293040 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq293033
  have eq293046 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq293040
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq293040
    | exact resolve eq293040 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq293040
  have eq293074 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq274279 eq293046
    | exact resolve eq293046 eq274279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274279 eq293046
  have eq293100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq283863 eq293074
    | exact resolve eq293074 eq283863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283863 eq293074
  have eq293126 : False := by grind
  exact eq293126

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pxx_pxy_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law909 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq9
    | (have j1 := eq53 X1 X0
       grind)
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq125 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k X1 (M.op X1 X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq67
    | (have j0 := eq67 (M.op X1 X0) X1
       grind)
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1194 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq125 (M.op X0 X0) X1
       have i₂ := eq67 X0 X1
       grind)
    | exact superpose eq67 eq125
    | (have j0 := eq125 X0 X0
       have j1 := eq67 X0 X1
       grind)
    | exact resolve eq125 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq125
  have eq1217 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1194 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1221 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1217 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1217 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1217 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq2210 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1221 X1 (τ X0)
       grind)
    | exact superpose eq1221 eq17
    | exact resolve eq17 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq2217 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2210 X0 X1
       have i₂ := eq1221 (σ X1) X0
       grind)
    | exact superpose eq1221 eq2210
    | exact resolve eq2210 eq1221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221 eq2210
  have eq2407 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2217 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2217
    | exact resolve eq2217 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq3017 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2407 x y
       grind)
    | exact superpose eq2407 eq16
    | (have r₁ := eq16
       have r₂ := eq2407 x y
       grind)
    | exact resolve eq16 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407
  have eq3067 : False := by grind
  exact eq3067

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_y_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq62 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq22
    | exact resolve eq22 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq64 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq64
    | exact resolve eq64 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq98
    | exact resolve eq98 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq101 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq24 (M.op X1 X1) X0
       grind)
    | exact superpose eq24 eq96
    | exact resolve eq96 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq102 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq95
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq103 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1
       have i₂ := eq24 (M.op X1 X0) (M.op X1 X0)
       grind)
    | exact superpose eq24 eq94
    | exact resolve eq94 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq104 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 X1
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq100
    | exact resolve eq100 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq105 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X1 X1))) = (M.op X0 (M.op X1 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0 X1
       have i₂ := eq24 X1 X1
       grind)
    | exact superpose eq24 eq101
    | exact resolve eq101 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq102
    | exact resolve eq102 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq107 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X1
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq103
    | exact resolve eq103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq108 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq117 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108 y x
       grind)
    | exact superpose eq108 eq16
    | (have j1 := eq108 y x
       grind)
    | exact resolve eq16 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq340 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1 (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq97
    | exact resolve eq97 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (M.op X2 (τ (M.op X0 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq340 (M.op X0 X1) X2
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq340
    | exact resolve eq340 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq363 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (k X0 (σ (τ X0))) (k X0 (σ (τ X0)))) := by
    intro X0
    grind
  clear eq62
  have eq388 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq363 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq363
    | exact resolve eq363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq395 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
    intro X0
    grind
  clear eq388
  have eq397 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq395 X0
       have i₂ := eq24 (τ X0) (τ X0)
       grind)
    | exact superpose eq24 eq395
    | exact resolve eq395 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq398 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq397 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq397
    | exact resolve eq397 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq399 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op (τ X0) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq398 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq398
    | exact resolve eq398 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398
  have eq657 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq117
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq117
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq117
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq117
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq117 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq658 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by grind
  clear eq657
  have eq686 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq66
    | exact resolve eq66 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq820 : ∀ X0 : G, (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq106 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq106
    | exact resolve eq106 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq820 X0
       have i₂ := eq97 (M.op (τ X0) (τ X0)) (τ X0)
       grind)
    | exact superpose eq97 eq820
    | exact resolve eq820 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq820
  have eq869 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (σ (M.op (τ X0) (M.op (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq854 X0
       have i₂ := eq24 (τ X0) (τ X0)
       grind)
    | exact superpose eq24 eq854
    | exact resolve eq854 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq876 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (σ (M.op (τ X0) (τ (M.op X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq869 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq869
    | exact resolve eq869 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq869
  have eq879 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq876 X0
       have i₂ := eq399 X0
       grind)
    | exact superpose eq399 eq876
    | exact resolve eq876 eq399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399 eq876
  have eq882 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq879 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq879
    | exact resolve eq879 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq884 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq882 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq882
    | exact resolve eq882 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882
  have eq897 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq884 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq884
    | exact resolve eq884 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq884
  have eq1047 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (M.op X1 (σ X0)) (M.op X1 (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq107 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq107
    | exact resolve eq107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1334 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))))) = (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq105 X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0)))
       have i₂ := eq107 X0 X1
       grind)
    | exact superpose eq107 eq105
    | exact resolve eq105 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1413 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))))) = (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X1 X0) (M.op (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1334 X0 X1
       have i₂ := eq24 (M.op X1 (M.op X0 X0)) (M.op X1 X0)
       grind)
    | exact superpose eq24 eq1334
    | exact resolve eq1334 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1334
  have eq1448 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))))) = (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1413 X0 X1
       have i₂ := eq24 (M.op X0 X0) X1
       grind)
    | exact superpose eq24 eq1413
    | exact resolve eq1413 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413
  have eq1473 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0)))))) = (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X1 X0) (M.op X1 (M.op X0 (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1448 X0 X1
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq1448
    | exact resolve eq1448 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1448
  have eq1490 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X0) (M.op X1 (M.op X0 X0))) (M.op X1 X0))) = (M.op (M.op X0 X0) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1473 X1 X0
       have i₂ := eq104 X0 X1
       grind)
    | exact superpose eq104 eq1473
    | exact resolve eq1473 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1473
  have eq1504 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X1 X0))) = (M.op X1 (M.op (M.op X1 (M.op X0 (M.op X0 X0))) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1490 X0 X1
       have i₂ := eq105 X1 X0
       grind)
    | exact superpose eq105 eq1490
    | exact resolve eq1490 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq1490
  have eq3399 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq346 X1 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq346
    | exact resolve eq346 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq3606 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X1)) = (σ (M.op X0 (M.op X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (M.op X2 (M.op X2 X1))
       have i₂ := eq3399 X1 X2 X0
       grind)
    | exact superpose eq3399 eq11
    | exact resolve eq11 eq3399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3646 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (M.op (τ X1) (τ X1))) (σ (τ (M.op X0 (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq897 (τ X1)
       have i₂ := eq3399 X1 X0 (τ X1)
       grind)
    | exact superpose eq3399 eq897
    | exact resolve eq897 eq3399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq3399
  have eq3684 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (M.op (τ X1) (τ X1))) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3646 X0 X1
       have i₂ := eq11 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq11 eq3646
    | exact resolve eq3646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3646
  have eq3734 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3684 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq3684
    | exact resolve eq3684 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3684
  have eq3760 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3734 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq3734
    | exact resolve eq3734 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3734
  have eq9966 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ (M.op y y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq658
       grind)
    | exact superpose eq658 eq16
    | exact resolve eq16 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq9967 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9966
       have r₂ := eq22 x
       grind)
    | exact resolve eq9966 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9966
  have eq46245 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X2 (M.op X2 (τ X1))) (M.op X2 (M.op X2 (τ X1))))) = (M.op X3 (M.op (M.op X3 (M.op X0 (M.op X0 X1))) (M.op X3 (σ (M.op (M.op X2 (M.op X2 (τ X1))) (M.op X2 (M.op X2 (τ X1)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1047 (M.op X2 (M.op X2 (τ X1))) X3
       have i₂ := eq3606 X2 X1 X0
       grind)
    | exact superpose eq3606 eq1047
    | exact resolve eq1047 eq3606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq3606
  have eq46470 : ∀ X0 X1 X2 X3 : G, (σ (M.op X2 (M.op (M.op X2 (τ X1)) (M.op X2 (τ X1))))) = (M.op X3 (M.op (M.op X3 (M.op X0 (M.op X0 X1))) (M.op X3 (σ (M.op X2 (M.op (M.op X2 (τ X1)) (M.op X2 (τ X1)))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq46245 X0 X1 X1 X3
       have i₂ := eq24 (M.op X1 (τ X1)) X1
       grind)
    | exact superpose eq24 eq46245
    | exact resolve eq46245 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46245
  have eq46565 : ∀ X0 X1 X3 : G, (σ (τ X1)) = (M.op X3 (M.op (M.op X3 (M.op X0 (M.op X0 X1))) (M.op X3 (σ (τ X1))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq46470 X0 X1 X1 X3
       have i₂ := eq9 (τ X1) X1
       grind)
    | exact superpose eq9 eq46470
    | exact resolve eq46470 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46470
  have eq46640 : ∀ X0 X1 X3 : G, (M.op X3 (M.op (M.op X3 (M.op X0 (M.op X0 X1))) (M.op X3 X1))) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq46565 X0 X0 X3
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46565
    | exact resolve eq46565 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46565
  have eq87484 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 (M.op X0 (M.op X0 X0))) (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1504 X0 X1
       have i₂ := eq3760 X1 X0
       grind)
    | exact superpose eq3760 eq1504
    | exact resolve eq1504 eq3760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504 eq3760
  have eq354038 : (σ x) = (M.op (σ y) (M.op (σ (M.op y y)) (σ (M.op y y)))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq9967
       grind)
    | exact superpose eq9967 eq9
    | exact resolve eq9 eq9967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9967
  have eq354237 : (σ x) = (M.op (σ y) (σ (M.op (M.op y y) (M.op y y)))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq354038
       have i₂ := eq22 (M.op y y)
       grind)
    | exact superpose eq22 eq354038
    | exact resolve eq354038 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354038
  have eq354331 : (σ x) = (M.op (σ y) (σ (M.op y (M.op y y)))) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq354237
       have i₂ := eq24 y y
       grind)
    | exact superpose eq24 eq354237
    | exact resolve eq354237 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq354237
  have eq354385 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq354331
       have i₂ := eq686 y
       grind)
    | exact superpose eq686 eq354331
    | exact resolve eq354331 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq354331
  have eq354386 : (M.op y y) = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq354385
  have eq354653 : y = (M.op y (M.op (M.op y (M.op y (M.op y x))) (M.op y x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq87484 y y
       have i₂ := eq354386
       grind)
    | exact superpose eq354386 eq87484
    | exact resolve eq87484 eq354386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87484 eq354386
  have eq354689 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq354653
       have i₂ := eq46640 y x y
       grind)
    | exact superpose eq46640 eq354653
    | exact resolve eq354653 eq46640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46640 eq354653
  have eq355300 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq354689
       grind)
    | exact superpose eq354689 eq16
    | exact resolve eq16 eq354689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354689
  have eq355301 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq355300
       have r₂ := eq22 x
       grind)
    | exact resolve eq355300 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355300
  have eq355303 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq355301
       grind)
    | exact superpose eq355301 eq10
    | exact resolve eq10 eq355301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355301
  have eq355739 : x = y := by
    first
    | (have i₁ := eq355303
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq355303
    | exact resolve eq355303 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355303
  have eq355751 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq355739
       grind)
    | exact superpose eq355739 eq16
    | exact resolve eq16 eq355739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355739
  have eq355752 : False := by grind
  exact eq355752

/-- `Equation909`: `x = y ◇ ((y ◇ x) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation909 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law909 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law909.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X0))) = X0 := by
    intro X0 X1
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
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
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq63 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq63
    | exact resolve eq63 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq95 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq95
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq107 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq103 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq103
    | exact resolve eq103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq109
    | (have j0 := eq109 X0 X1
       grind)
    | exact resolve eq109 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq119 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq110 y x
       grind)
    | exact superpose eq110 eq16
    | (have j1 := eq110 y x
       grind)
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq297 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X1 (τ X0)
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq97
    | exact resolve eq97 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq301 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (M.op X2 (τ (M.op X0 (M.op X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq297 (M.op X0 X1) X2
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq297
    | exact resolve eq297 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq119
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq119
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq119
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq119
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq119 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq718 : x = y ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq717
  have eq745 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq66
    | exact resolve eq66 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq66
  have eq3201 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X2 (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301 X1 (M.op X1 X0) X2
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq301
    | exact resolve eq301 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq3390 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X1 (σ X0)))) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3201 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3201
    | exact resolve eq3201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201
  have eq6284 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X3 X1)) = (τ (τ (M.op X0 (M.op X0 (σ (σ X1)))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3390 X1 x X3
       have i₂ := eq3390 (σ X1) X0 x
       grind)
    | exact superpose eq3390 eq3390
    | exact resolve eq3390 eq3390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6321 : ∀ X0 X1 : G, (M.op (σ X0) (σ (M.op X0 (M.op X0 X0)))) = (τ (M.op X1 (M.op X1 (σ (σ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3390 (σ (M.op X0 X0)) X1 (σ X0)
       have i₂ := eq107 X0
       grind)
    | exact superpose eq107 eq3390
    | exact resolve eq3390 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq3390
  have eq6505 : ∀ X0 X1 : G, (σ X0) = (τ (M.op X1 (M.op X1 (σ (σ (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6321 X0 X1
       have i₂ := eq745 X0
       grind)
    | exact superpose eq745 eq6321
    | exact resolve eq6321 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq6321
  have eq7748 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq718
       grind)
    | exact superpose eq718 eq16
    | exact resolve eq16 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq7749 : (M.op y y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7748
       have r₂ := eq22 x
       grind)
    | exact resolve eq7748 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7748
  have eq304492 : ∀ X0 : G, (σ y) = (τ (M.op X0 (M.op X0 (σ (σ (M.op x x)))))) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq6505 y X0
       have i₂ := eq7749
       grind)
    | exact superpose eq7749 eq6505
    | exact resolve eq6505 eq7749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7749
  have eq304644 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq304492 x
       have i₂ := eq6505 x x
       grind)
    | exact superpose eq6505 eq304492
    | exact resolve eq304492 eq6505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304492
  have eq304645 : (σ x) = (σ y) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq304644
  have eq304676 : (σ (M.op y y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq22 y
       have i₂ := eq304645
       grind)
    | exact superpose eq304645 eq22
    | exact resolve eq22 eq304645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304645
  have eq305076 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq304676
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq304676
    | exact resolve eq304676 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304676
  have eq305077 : (σ (M.op y y)) = (σ (M.op x x)) := by grind
  clear eq305076
  have eq305485 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op y y))) = (τ (τ (M.op X1 (M.op X1 (σ (σ (M.op x x))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq6284 X1 (M.op y y) X0
       have i₂ := eq305077
       grind)
    | exact superpose eq305077 eq6284
    | exact resolve eq6284 eq305077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6284 eq305077
  have eq305540 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op y y))) = (τ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq305485 X0 x
       have i₂ := eq6505 x x
       grind)
    | exact superpose eq6505 eq305485
    | exact resolve eq305485 eq6505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6505 eq305485
  have eq305780 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq305540 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq305540
    | exact resolve eq305540 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305540
  have eq305819 : x = y := by
    first
    | (have i₁ := eq305780 x
       have i₂ := eq97 x y
       grind)
    | exact superpose eq97 eq305780
    | exact resolve eq305780 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq305780
  have eq305830 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq305819
       grind)
    | exact superpose eq305819 eq16
    | exact resolve eq16 eq305819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305819
  have eq305831 : False := by grind
  exact eq305831
