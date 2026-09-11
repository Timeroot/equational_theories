import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1489`: `x = (y ◇ x) ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1489 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1489 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1489.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq82 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X0 X1) (k X0 X1)
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq98 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq104 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq98 X0 (τ X1)
       grind)
    | exact superpose eq98 eq19
    | (have j1 := eq98 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq98 (σ X0) (σ X1)
       grind)
    | exact superpose eq98 eq15
    | (have j1 := eq98 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq242 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104
    | exact resolve eq104 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq267 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq242
    | (have j0 := eq242 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq242 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq798 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq105 x y
       grind)
    | exact superpose eq105 eq16
    | (have j1 := eq105 x y
       grind)
    | exact resolve eq16 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq863 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq798
       have i₂ := eq267 y x
       grind)
    | exact superpose eq267 eq798
    | (have j1 := eq267 (σ x) (σ y)
       grind)
    | (have r₁ := eq798
       have r₂ := eq267 y x
       grind)
    | (have r₁ := eq798
       have r₂ := eq267 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq798
       have r₂ := eq267 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq798 eq267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq798
  have eq864 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq863
  have eq869 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq864
       grind)
    | exact superpose eq864 eq10
    | exact resolve eq10 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq902 : x = y ∨ x = y := by
    first
    | (have i₁ := eq869
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq869
    | exact resolve eq869 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq903 : x = y := by grind
  clear eq902
  have eq931 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq903
       grind)
    | exact superpose eq903 eq16
    | exact resolve eq16 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq932 : False := by grind
  exact eq932

/-- `Equation1543`: `x = (y ◇ y) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_x_pxy_pxx_pxy_Equation1543 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1543 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1543.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X2 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  clear eq24
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X1 X1) X0) X2 (M.op X1 X1)
       have i₂ := eq16 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (k X0 X1))) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq180
       grind)
    | exact superpose eq180 eq41
    | exact resolve eq41 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq194 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq193
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq193
    | exact resolve eq193 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq196 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq194
    | exact resolve eq194 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq181
    | exact resolve eq181 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq200
       have r₂ := eq27
       grind)
    | exact resolve eq200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq213 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq203 eq176
    | exact resolve eq176 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq213 eq213
    | exact resolve eq213 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : y = (M.op (σ y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq213 eq175
    | exact resolve eq175 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq225 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq213 eq16
    | exact resolve eq16 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq228 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq220
  have eq247 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq228 eq225
    | exact resolve eq225 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq225 eq225
    | exact resolve eq225 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq225 eq16
    | exact resolve eq16 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (σ y) (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq248 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq256 : (M.op (σ x) (σ x)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq247
  have eq266 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ y) (M.op X0 X0)) X1) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq252 X1 (M.op X0 X0)
       have i₂ := eq252 (M.op X0 X0) X0
       grind)
    | exact superpose eq252 eq252
    | exact resolve eq252 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ y) (M.op X0 X0)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq266 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq376 : ∀ X0 : G, (M.op (σ y) y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq224 eq255
    | exact resolve eq255 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq255 X0 sF3
       grind)
    | exact superpose eq255 eq255
    | exact resolve eq255 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq256
       have i₂ := eq255 sF3 sF3
       grind)
    | exact superpose eq255 eq256
    | exact resolve eq256 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq396 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ y) X1))) = X1 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq225 sF3 X1
       have i₂ := eq255 (M.op sF3 X1) sF3
       grind)
    | exact superpose eq255 eq225
    | exact resolve eq225 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq404 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op (σ y) X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq396 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq406 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq394 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq411 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have j0 := eq384 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq418 : ∀ X0 : G, (M.op (σ y) y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq462 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 X0)) = (M.op X1 (M.op (σ y) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq404 eq225
    | exact resolve eq225 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 X0)) = (M.op X1 (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq538 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq406 eq225
    | exact resolve eq225 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq1107 : (M.op (σ x) (M.op (σ y) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq471
    | (have j0 := eq471 (σ y) (σ x)
       grind)
    | exact resolve eq471 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq471 eq228
    | exact resolve eq228 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq1145 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op X0 X1))) = X1 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq471 eq404
    | exact resolve eq404 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq1145 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1189 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq1136
  have eq1235 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203 eq1107
    | exact resolve eq1107 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq1266 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1349 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1365 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1349
       have i₂ := eq1266 sF2
       grind)
    | exact superpose eq1266 eq1349
    | exact resolve eq1349 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1349
  have eq1476 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq176 eq1182
    | exact resolve eq1182 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1484 : y = (M.op x (M.op (σ y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1182 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1182
    | (have j0 := eq1182 x y
       grind)
    | exact resolve eq1182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1593 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 X0) (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1476 X0
       have i₂ := eq1266 sF3
       grind)
    | exact superpose eq1266 eq1476
    | exact resolve eq1476 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1596 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k X0 X0) (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1593 X0
       have i₂ := eq1266 X0
       grind)
    | exact superpose eq1266 eq1593
    | exact resolve eq1593 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1593
  have eq1598 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (k X0 X0) (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq203 eq1596
    | exact resolve eq1596 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1599 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (k X0 X0) (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1598 X0
       have i₂ := eq1266 sF2
       grind)
    | exact superpose eq1266 eq1598
    | exact resolve eq1598 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1612 : (M.op (σ y) (M.op x y)) = (M.op x (M.op (σ y) y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1484 eq1182
    | exact resolve eq1182 eq1484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182 eq1484
  have eq1613 : (M.op (σ y) (M.op x y)) = (M.op x (M.op (σ y) y)) ∨ x = (M.op x y) := by grind
  clear eq1612
  have eq1630 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1235 eq16
    | exact resolve eq16 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1634 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1235 eq411
    | exact resolve eq411 eq1235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq1235
  have eq1639 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ y) (σ y)))) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634
  have eq1644 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (σ x))) = (M.op X0 (M.op X0 (k (σ y) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1639 X0
       have i₂ := eq1266 sF3
       grind)
    | exact superpose eq1266 eq1639
    | exact resolve eq1639 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq1647 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (k X0 X0) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1630 X0
       have i₂ := eq1266 X0
       grind)
    | exact superpose eq1266 eq1630
    | exact resolve eq1630 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq1651 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (k (σ y) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1189 eq1644
    | exact resolve eq1644 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644
  have eq1653 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (k X0 X0) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1647 X0
       have i₂ := eq1266 sF3
       grind)
    | exact superpose eq1266 eq1647
    | exact resolve eq1647 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1655 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (k X0 X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1189 eq1653
    | exact resolve eq1653 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1189 eq1653
  have eq1711 : ∀ X0 : G, (M.op (σ y) (k (σ y) (σ y))) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1651 eq404
    | exact resolve eq404 eq1651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404 eq1651
  have eq1714 : ∀ X0 : G, (M.op (σ y) (k (σ y) (σ y))) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1711 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711
  have eq1740 : (M.op (σ x) (σ x)) = (M.op (σ y) (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq406 eq1714
    | exact resolve eq1714 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq1714
  have eq1752 : (k (σ x) (σ x)) = (M.op (σ y) (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1740
       have i₂ := eq1266 sF2
       grind)
    | exact superpose eq1266 eq1740
    | exact resolve eq1740 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1789 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X0) (M.op (k X1 X1) (k (σ y) (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1655 eq16
    | exact resolve eq16 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1806 : ∀ X0 X1 : G, (σ y) = (M.op (k X0 X0) (M.op (k X1 X1) (k (σ y) (σ y)))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1789 X0 X1
       have i₂ := eq1266 X0
       grind)
    | exact superpose eq1266 eq1789
    | exact resolve eq1789 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1789
  have eq1813 : ∀ X0 : G, (σ y) = (M.op (k X0 X0) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1599 eq1806
    | exact resolve eq1806 eq1599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1599 eq1806
  have eq1820 : ∀ X0 : G, (M.op (σ y) y) = (M.op (M.op X0 X0) (M.op x (M.op (σ y) (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1613 eq16
    | exact resolve eq16 eq1613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613
  have eq1839 : ∀ X0 : G, (M.op (σ y) y) = (M.op (k X0 X0) (M.op x (M.op (σ y) (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1820 X0
       have i₂ := eq1266 X0
       grind)
    | exact superpose eq1266 eq1820
    | exact resolve eq1820 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq1841 : ∀ X0 : G, (M.op (σ y) y) = (M.op (k X0 X0) (M.op (σ y) (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq471 eq1839
    | exact resolve eq1839 eq471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471 eq1839
  have eq1842 : ∀ X0 : G, (M.op (σ y) y) = (M.op (k X0 X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq224 eq1841
    | exact resolve eq1841 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq2587 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ x) (σ x)) (σ y)) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq549 eq290
    | exact resolve eq290 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq549
  have eq2624 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ x) (σ x)) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2587 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq2649 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (k (σ x) (σ x)) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2624 X0
       have i₂ := eq1266 sF2
       grind)
    | exact superpose eq1266 eq2624
    | exact resolve eq2624 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2624
  have eq2664 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (k (σ y) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1655 eq2649
    | exact resolve eq2649 eq1655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1655 eq2649
  have eq2696 : ∀ X0 X1 : G, (M.op (M.op (σ y) (k (σ y) (σ y))) (M.op X0 (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2664 eq16
    | exact resolve eq16 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664
  have eq2819 : ∀ X0 X1 : G, (M.op (k (σ x) (σ x)) (M.op X0 (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1752 eq2696
    | exact resolve eq2696 eq1752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752 eq2696
  have eq3037 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (k X0 X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq252 X1 X0
       have i₂ := eq1266 X0
       grind)
    | exact superpose eq1266 eq252
    | exact resolve eq252 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq3041 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq1266 X0
       grind)
    | exact superpose eq1266 eq16
    | exact resolve eq16 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3042 : ∀ X0 : G, (M.op (σ y) (M.op X0 (k X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq225 X0 X0
       have i₂ := eq1266 X0
       grind)
    | exact superpose eq1266 eq225
    | exact resolve eq225 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq3063 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1813 sF2
       have i₂ := eq1266 (k sF2 sF2)
       grind)
    | exact superpose eq1266 eq1813
    | exact resolve eq1813 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813
  have eq3094 : ∀ X0 X1 : G, (M.op (k X1 X1) (M.op X0 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3041 X0 X1
       have i₂ := eq1266 X1
       grind)
    | exact superpose eq1266 eq3041
    | exact resolve eq3041 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041
  have eq6718 : ∀ X0 X1 : G, (k (M.op X1 X1) (M.op X1 X1)) = (M.op (M.op X0 X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1266 (M.op X1 X1)
       have i₂ := eq178 (M.op X1 X1) X0 X1
       grind)
    | (have i₁ := eq1266 (M.op X1 X1)
       have i₂ := eq178 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq178 eq1266
    | exact resolve eq1266 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq6805 : ∀ X0 X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op (M.op X0 X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6718 X0 X0
       have i₂ := eq1266 X0
       grind)
    | exact superpose eq1266 eq6718
    | exact resolve eq6718 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6718
  have eq6956 : ∀ X0 X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op (k X0 X0) (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6805 X0 X1
       have i₂ := eq1266 X0
       grind)
    | exact superpose eq1266 eq6805
    | exact resolve eq6805 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6805
  have eq12115 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203 eq1365
    | (have r₁ := eq1365
       have r₂ := eq203
       grind)
    | exact resolve eq1365 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq1365
  have eq12116 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq12115
  have eq12117 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq12116
    | exact resolve eq12116 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12116
  have eq12136 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12117 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq12117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12117
  have eq12176 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | (have r₁ := eq12136
       have r₂ := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq12136 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12136
  have eq12190 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12176
    | exact resolve eq12176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12176
  have eq12195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq12190
    | exact resolve eq12190 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq12190
  have eq12197 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12195
       have r₂ := eq27
       grind)
    | exact resolve eq12195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12195
  have eq12198 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12197 eq98
    | exact resolve eq98 eq12197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12208 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12197 eq3063
    | exact resolve eq3063 eq12197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3063 eq12197
  have eq12272 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq12208
  have eq12285 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq12198
    | exact resolve eq12198 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12198
  have eq12302 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3037 x X0
       have i₂ := eq12285
       grind)
    | exact superpose eq12285 eq3037
    | exact resolve eq3037 eq12285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3037
  have eq12305 : x = (M.op (σ y) (M.op x (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3042 x
       have i₂ := eq12285
       grind)
    | exact superpose eq12285 eq3042
    | exact resolve eq3042 eq12285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3042
  have eq12319 : x = (M.op (σ y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq12305
  have eq12322 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12302 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12302
  have eq12453 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12272 eq134
    | exact resolve eq134 eq12272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq12272
  have eq12504 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq12453
    | exact resolve eq12453 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12453
  have eq12518 : (M.op (σ y) y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12504 eq1842
    | exact resolve eq1842 eq12504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq12554 : (M.op (σ y) y) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq12518
  have eq12575 : (k y y) = (M.op (σ y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12554
       have i₂ := eq1266 y
       grind)
    | exact superpose eq1266 eq12554
    | exact resolve eq12554 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12554
  have eq12780 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12319 eq224
    | exact resolve eq224 eq12319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq12793 : (M.op (σ y) y) = (M.op (σ y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12319 eq418
    | exact resolve eq418 eq12319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418 eq12319
  have eq12809 : (M.op (σ y) y) = (M.op (σ y) x) ∨ x = (M.op x y) := by grind
  clear eq12793
  have eq12822 : x = (M.op x y) ∨ x = y := by grind
  clear eq12780
  have eq12830 : (M.op (σ y) y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12322 eq12809
    | exact resolve eq12809 eq12322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12322 eq12809
  have eq12841 : (k y y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12575 eq12830
    | exact resolve eq12830 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12575 eq12830
  have eq12845 : (k x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12822 eq12841
    | exact resolve eq12841 eq12822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12841
  have eq12848 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12285 eq12845
    | exact resolve eq12845 eq12285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12845
  have eq12899 : x = (M.op (k (σ x) (σ x)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12848 eq2819
    | exact resolve eq2819 eq12848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2819 eq12848
  have eq12902 : x = (M.op (k (σ x) (σ x)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq12899
  have eq12910 : x = (M.op (k (σ x) (σ x)) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12902
       have i₂ := eq1266 sF0
       grind)
    | exact superpose eq1266 eq12902
    | exact resolve eq12902 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12902
  have eq12919 : x = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12910
       have i₂ := eq6956 sF2 sF0
       grind)
    | exact superpose eq6956 eq12910
    | exact resolve eq12910 eq6956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6956 eq12910
  have eq12928 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12504 eq12919
    | exact resolve eq12919 eq12504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12504 eq12919
  have eq12936 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12822 eq12928
    | exact resolve eq12928 eq12822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12822 eq12928
  have eq12940 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12285 eq12936
    | exact resolve eq12936 eq12285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12285 eq12936
  have eq12941 : x = (M.op x y) := by grind
  clear eq12940
  have eq12946 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12941
       grind)
    | exact superpose eq12941 eq18
    | exact resolve eq18 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq12947 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq12941
       grind)
    | exact superpose eq12941 eq22
    | exact resolve eq22 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq12955 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12947 eq20
    | exact resolve eq20 eq12947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12947
  have eq13015 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12946 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | (have r₁ := eq12 (M.op x y) y
       have r₂ := eq12946
       grind)
    | exact resolve eq12 eq12946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13024 : (M.op x y) = (M.op y (M.op x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq13015
  have eq13026 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq13024
       have i₂ := eq1266 sF0
       grind)
    | exact superpose eq1266 eq13024
    | exact resolve eq13024 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13024
  have eq19603 : (k (σ (M.op x y)) (σ y)) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq13026 eq41
    | exact resolve eq41 eq13026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13026
  have eq19607 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq42 eq19603
    | exact resolve eq19603 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq19603
  have eq19610 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq12955 eq19607
    | exact resolve eq19607 eq12955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19607
  have eq19613 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20 eq19610
    | exact resolve eq19610 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19610
  have eq19616 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq12955 eq19613
    | exact resolve eq19613 eq12955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19613
  have eq19627 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19616 eq183
    | (have j0 := eq183 (σ x) (σ y) x
       grind)
    | exact resolve eq183 eq19616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq19616
  have eq19630 : ∀ X0 : G, (σ y) = (M.op (k X0 X0) (M.op (σ x) (k (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq19627 X0
       have i₂ := eq1266 X0
       grind)
    | exact superpose eq1266 eq19627
    | exact resolve eq19627 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19627
  have eq19633 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq19630 x
       have i₂ := eq3094 sF2 x
       grind)
    | exact superpose eq3094 eq19630
    | exact resolve eq19630 eq3094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3094 eq19630
  have eq19636 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq19633
    | exact resolve eq19633 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19633
  have eq19643 : (M.op x y) ≠ (M.op (M.op x y) y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19636 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | exact resolve eq13 eq19636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19636
  have eq19664 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq28 (M.op x y) y
       grind)
    | (have r₁ := eq19643
       have r₂ := eq28 (M.op x y) y
       grind)
    | exact resolve eq19643 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19643
  have eq19672 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12946 eq19664
    | exact resolve eq19664 eq12946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19664
  have eq19700 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19672 eq41
    | exact resolve eq41 eq19672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq19672
  have eq19705 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19700
    | exact resolve eq19700 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19700
  have eq19708 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12955 eq19705
    | exact resolve eq19705 eq12955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19705
  have eq19731 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19708 eq181
    | exact resolve eq181 eq19708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq19708
  have eq19737 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq19731
  have eq19745 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19737 eq27
    | exact resolve eq27 eq19737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19737
  have eq19747 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq19745
       have r₂ := eq12955
       grind)
    | exact resolve eq19745 eq12955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12955 eq19745
  have eq19749 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq19747 eq26
    | exact resolve eq26 eq19747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq19750 : y = (τ (σ x)) := by
    first
    | exact superpose eq19747 eq32
    | exact resolve eq32 eq19747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq19747
  have eq19879 : x = y := by
    first
    | exact superpose eq30 eq19750
    | exact resolve eq19750 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19750
  have eq19880 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq19749
       have i₂ := eq1266 sF2
       grind)
    | exact superpose eq1266 eq19749
    | exact resolve eq19749 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19749
  have eq19888 : y = (M.op x y) := by
    first
    | (have i₁ := eq19879
       have i₂ := eq12941
       grind)
    | exact superpose eq12941 eq19879
    | exact resolve eq19879 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19879
  have eq19923 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12946
       have i₂ := eq19888
       grind)
    | exact superpose eq19888 eq12946
    | exact resolve eq12946 eq19888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12946 eq19888
  have eq19928 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq19923
       have i₂ := eq1266 sF0
       grind)
    | exact superpose eq1266 eq19923
    | exact resolve eq19923 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq19923
  have eq19935 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19880 eq98
    | exact resolve eq98 eq19880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq19880
  have eq19990 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq19935
       have i₂ := eq12941
       grind)
    | exact superpose eq12941 eq19935
    | exact resolve eq19935 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12941 eq19935
  have eq19993 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq19928 eq19990
    | exact resolve eq19990 eq19928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19928 eq19990
  have eq19998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19993 eq14
    | exact resolve eq14 eq19993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19993
  have eq19999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq19998
    | exact resolve eq19998 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19998
  have eq20002 : False := by grind
  exact eq20002

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyx_x_pyx_pxy_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  clear eq36
  have eq47 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq72 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq69
    | exact resolve eq69 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq72
    | exact resolve eq72 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq74 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
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
  have eq84 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq200 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq47 (M.op y y)
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y y))) := by
    intro X0
    first
    | exact superpose eq200 eq14
    | exact resolve eq14 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq208 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ y) X0)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 (M.op X0 (M.op X1 X0)) (M.op x X1)
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq53 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq84 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq84
    | (have j0 := eq84 (σ X0)
       grind)
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84 x
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 x
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq430 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq84 y
       grind)
    | exact superpose eq84 eq90
    | (have j1 := eq84 y
       grind)
    | exact resolve eq90 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq528 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1)))) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1)))) X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49 X1 X2 (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1)))) X0))
       have i₂ := eq49 (M.op X1 (M.op X2 X1)) X3 X0
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X1 X2
       have i₂ := eq49 X2 X3 X0
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq49 y X1 X0
       grind)
    | exact superpose eq49 eq47
    | exact resolve eq47 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq49 sF3 x x
       grind)
    | exact superpose eq49 eq48
    | exact resolve eq48 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq660 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 (M.op X1 X0)) X0) X2)) = (M.op (M.op X3 (M.op X0 (M.op X1 X0))) (M.op (M.op X2 (M.op (M.op (M.op X0 (M.op X1 X0)) X0) X2)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X2 X3 (M.op x (M.op x X1)) (M.op (M.op X0 (M.op X1 X0)) X0)
       have i₂ := eq52 X0 x x X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op (M.op y (M.op x y)) y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq683 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y X0)) X0) = (M.op (M.op X1 (M.op X2 (M.op x y))) (M.op (M.op (M.op X0 (M.op y X0)) X0) (M.op X0 (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq47 eq52
    | exact resolve eq52 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq53 (M.op (M.op X0 (M.op X0 X0)) X0) x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op X1 (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 x (M.op (M.op X0 (M.op X1 X0)) X0)
       have i₂ := eq52 X0 X1 x X1
       grind)
    | exact superpose eq52 eq49
    | exact resolve eq49 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq911 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq221 sF4
       have i₂ := eq53 sF4 sF3
       grind)
    | exact superpose eq53 eq221
    | exact resolve eq221 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq1408 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq234 X0 x x
       grind)
    | exact superpose eq234 eq53
    | exact resolve eq53 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1415 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1408 X0
       have i₂ := eq234 X0 X0 X0
       grind)
    | exact superpose eq234 eq1408
    | exact resolve eq1408 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq3691 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq673 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1415 sF0
       grind)
    | exact superpose eq1415 eq673
    | exact resolve eq673 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3720 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq3691
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq3691
    | exact resolve eq3691 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3691
  have eq3727 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3720 eq673
    | exact resolve eq673 eq3720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq3755 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3727 eq14
    | exact resolve eq14 eq3727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3787 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq674 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1415 sF4
       grind)
    | exact superpose eq1415 eq674
    | exact resolve eq674 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3816 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3787
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3787
    | exact resolve eq3787 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3787
  have eq3839 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3816 eq674
    | exact resolve eq674 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq3933 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3755 eq47
    | exact resolve eq47 eq3755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq3755
  have eq3967 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq3933 eq3727
    | exact resolve eq3727 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3727
  have eq4102 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq911 eq208
    | exact resolve eq208 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq911
  have eq4138 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq4102 X0
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq4102
    | exact resolve eq4102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4102
  have eq4139 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4138 x
       have i₂ := eq53 sF4 x
       grind)
    | exact superpose eq53 eq4138
    | exact resolve eq4138 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4138
  have eq4140 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3816 eq4139
    | exact resolve eq4139 eq3816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3816 eq4139
  have eq4141 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4140 eq3839
    | exact resolve eq3839 eq4140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3839
  have eq4659 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq425 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq6211 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq528 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq234 X0 x X2
       grind)
    | exact superpose eq234 eq528
    | exact resolve eq528 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq6314 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq6211 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq6211
    | exact resolve eq6211 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6211
  have eq6326 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq6314 X0 x
       have i₂ := eq53 X0 x
       grind)
    | exact superpose eq53 eq6314
    | exact resolve eq6314 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6314
  have eq7210 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq683 X0 X1 X2 X3
       have i₂ := eq6326 X0
       grind)
    | exact superpose eq6326 eq683
    | exact resolve eq683 eq6326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq7312 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7210 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq234 X0 x x
       grind)
    | exact superpose eq234 eq7210
    | exact resolve eq7210 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7534 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7312 X0 X1 X2
       have i₂ := eq234 X0 X0 X0
       grind)
    | exact superpose eq234 eq7312
    | exact resolve eq7312 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7312
  have eq7572 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7534 X0 X1 X2
       have i₂ := eq6326 X0
       grind)
    | exact superpose eq6326 eq7534
    | exact resolve eq7534 eq6326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6326 eq7534
  have eq7634 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7572 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq7572
    | (have j0 := eq7572 y X0 x
       grind)
    | exact resolve eq7572 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7646 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq7572
    | (have j0 := eq7572 (σ y) X0 (σ x)
       grind)
    | exact resolve eq7572 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7662 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7572 (M.op X1 X0) (M.op x X1) X0
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq7572
    | exact resolve eq7572 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7721 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq673 X0
       have i₂ := eq7572 X0 X0 sF0
       grind)
    | exact superpose eq7572 eq673
    | exact resolve eq673 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq7939 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq692 X0
       have i₂ := eq7572 X0 X0 X0
       grind)
    | exact superpose eq7572 eq692
    | exact resolve eq692 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq8357 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 X1
       have i₂ := eq7572 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq7572 eq535
    | exact resolve eq535 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq8558 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 y x X0
       have i₂ := eq8357 X0 x
       grind)
    | exact superpose eq8357 eq49
    | exact resolve eq49 eq8357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8357
  have eq8691 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq8558 (M.op X0 X0)
       have i₂ := eq7939 X0
       grind)
    | exact superpose eq7939 eq8558
    | exact resolve eq8558 eq7939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7939
  have eq8694 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8558 (M.op X0 (M.op X0 X0))
       have i₂ := eq234 X0 X0 X0
       grind)
    | exact superpose eq234 eq8558
    | exact resolve eq8558 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8840 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq8694 X0
       grind)
    | exact superpose eq8694 eq14
    | exact resolve eq14 eq8694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8927 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq8694 eq14
    | exact resolve eq14 eq8694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8956 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8927 X0 X1
       have i₂ := eq14 X0 sF0 X0
       grind)
    | exact superpose eq14 eq8927
    | exact resolve eq8927 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8927
  have eq9070 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq536 X0 X1
       have i₂ := eq7572 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq7572 eq536
    | exact resolve eq536 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq9367 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq9070 eq49
    | exact resolve eq49 eq9070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9070
  have eq9517 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq9367 (M.op X0 (M.op X0 X0))
       have i₂ := eq234 X0 X0 X0
       grind)
    | exact superpose eq234 eq9367
    | exact resolve eq9367 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9367
  have eq9830 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op x y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq681 X0 X1 X2
       have i₂ := eq8956 (M.op y sF0) (M.op y sF0)
       grind)
    | exact superpose eq8956 eq681
    | exact resolve eq681 eq8956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681 eq8956
  have eq9831 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3967 eq9830
    | exact resolve eq9830 eq3967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3967 eq9830
  have eq9832 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7634 eq9831
    | exact resolve eq9831 eq7634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9831
  have eq9935 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq9517 eq14
    | exact resolve eq14 eq9517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9517
  have eq9964 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9935 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq9935
    | exact resolve eq9935 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9935
  have eq10479 : (M.op y y) = (M.op x (M.op y (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq9832 (M.op x (M.op x x)) x x
       have i₂ := eq49 x x x
       grind)
    | exact superpose eq49 eq9832
    | exact resolve eq9832 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9832
  have eq10610 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq9964 eq682
    | exact resolve eq682 eq9964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq9964
  have eq10611 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4141 eq10610
    | exact resolve eq10610 eq4141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4141 eq10610
  have eq10612 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7646 eq10611
    | exact resolve eq10611 eq7646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7646 eq10611
  have eq10640 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq10612 (M.op x (M.op x x)) x sF2
       have i₂ := eq49 x x sF2
       grind)
    | exact superpose eq49 eq10612
    | exact resolve eq10612 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10612
  have eq10727 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 x
       have i₂ := eq7572 X0 X0 x
       grind)
    | exact superpose eq7572 eq694
    | exact resolve eq694 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq10835 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X1) (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10727 (M.op X0 (M.op X1 X0)) (M.op X2 X1)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq10727
    | exact resolve eq10727 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10727
  have eq11132 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X1) (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10835 X0 X1 X2
       have i₂ := eq7572 X0 X0 X1
       grind)
    | exact superpose eq7572 eq10835
    | exact resolve eq10835 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10835
  have eq11234 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11132 X0 X1 X2
       have i₂ := eq7210 X0 X1 (M.op X0 (M.op X1 X0)) X0
       grind)
    | exact superpose eq7210 eq11132
    | exact resolve eq11132 eq7210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11132
  have eq11294 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op (M.op X2 X1) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11234 X0 X1 X2
       have i₂ := eq222 X0 X1
       grind)
    | exact superpose eq222 eq11234
    | exact resolve eq11234 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq11234
  have eq13738 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq533 X0 X1 X2 X3
       have i₂ := eq7572 X0 X0 (M.op X2 (M.op X3 X2))
       grind)
    | exact superpose eq7572 eq533
    | exact resolve eq533 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq14237 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 x X2
       have i₂ := eq13738 X2 X0 X1 x
       grind)
    | exact superpose eq13738 eq49
    | exact resolve eq49 eq13738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13738
  have eq14861 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op (M.op X1 X0) (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq3933 eq14237
    | exact resolve eq14237 eq3933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14862 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq4140 eq14237
    | exact resolve eq14237 eq4140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4140 eq14237
  have eq16817 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op x y))) (M.op (M.op X0 X0) (M.op X0 (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq685 X0 X1 X2
       have i₂ := eq7572 X0 X0 y
       grind)
    | exact superpose eq7572 eq685
    | exact resolve eq685 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq23440 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 (M.op X1 X0)) X0) X2)) = (M.op (M.op X3 (M.op X0 (M.op X1 X0))) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq660 X0 X1 X2 X3
       have i₂ := eq7572 X2 X2 (M.op (M.op X0 (M.op X1 X0)) X0)
       grind)
    | exact superpose eq7572 eq660
    | exact resolve eq660 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq23441 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X2)) = (M.op (M.op X3 (M.op X0 (M.op X1 X0))) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23440 X0 X1 X2 X3
       have i₂ := eq7572 X0 X0 X1
       grind)
    | exact superpose eq7572 eq23440
    | exact resolve eq23440 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23440
  have eq23895 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23441 X0 (M.op x (M.op x x)) X1 x
       have i₂ := eq49 x x X0
       grind)
    | exact superpose eq49 eq23441
    | exact resolve eq23441 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32006 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1)))) X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq530 X0 X1 X2 X3
       have i₂ := eq7572 X0 X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1))))
       grind)
    | exact superpose eq7572 eq530
    | exact resolve eq530 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq32563 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X0 (M.op X2 X0)) x X1
       have i₂ := eq32006 X1 X0 X2 x
       grind)
    | exact superpose eq32006 eq49
    | exact resolve eq49 eq32006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq32006
  have eq37319 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X1 X1) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23441 X1 X3 (M.op X0 (M.op X0 X0)) X2
       have i₂ := eq32563 X0 X0 X0
       grind)
    | exact superpose eq32563 eq23441
    | exact resolve eq23441 eq32563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23441 eq32563
  have eq37390 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) = (M.op X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37319 X0 X1 X2 X3
       have i₂ := eq23895 X1 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23895 eq37319
    | exact resolve eq37319 eq23895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23895 eq37319
  have eq37562 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 (M.op X3 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37390 X0 X1 X2 X3
       have i₂ := eq234 X0 X0 X0
       grind)
    | exact superpose eq234 eq37390
    | exact resolve eq37390 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq37390
  have eq53839 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X0 (M.op X0 X0))) (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op x y))) (M.op (M.op (M.op (M.op x y) (M.op X0 (M.op X0 X0))) (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) (M.op (M.op (M.op x y) (M.op X0 (M.op X0 X0))) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq8691 eq16817
    | exact resolve eq16817 eq8691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8691 eq16817
  have eq53953 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X0 (M.op X0 X0))) (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op x y))) (M.op (M.op (M.op (M.op x y) (M.op X0 (M.op X0 X0))) (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53839 X2 X1 X2
       have i₂ := eq7572 (M.op X2 X2) sF0 X2
       grind)
    | exact superpose eq7572 eq53839
    | exact resolve eq53839 eq7572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7572 eq53839
  have eq54043 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X0 (M.op X0 X0))) (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op x y))) (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53953 X1 X1 X2
       have i₂ := eq7210 (M.op X1 X1) X1 (M.op sF0 (M.op X1 (M.op X1 X1))) sF0
       grind)
    | exact superpose eq7210 eq53953
    | exact resolve eq53953 eq7210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7210 eq53953
  have eq54108 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X0 (M.op X0 X0))) (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op x y))) (M.op y (M.op (M.op x y) (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54043 X0 X1 X2
       have i₂ := eq8694 (M.op X0 X0)
       grind)
    | exact superpose eq8694 eq54043
    | exact resolve eq54043 eq8694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8694 eq54043
  have eq54148 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op X0 (M.op X0 X0))) (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq8558 eq54108
    | exact resolve eq54108 eq8558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8558 eq54108
  have eq54172 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54148 X0 X1 X2
       have i₂ := eq7662 (M.op X0 (M.op X0 X0)) sF0
       grind)
    | exact superpose eq7662 eq54148
    | exact resolve eq54148 eq7662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54148
  have eq54188 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq7721 eq54172
    | exact resolve eq54172 eq7721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54172
  have eq54201 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54188 X0 X1 X2
       have i₂ := eq7662 (M.op X0 X0) X0
       grind)
    | exact superpose eq7662 eq54188
    | exact resolve eq54188 eq7662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7662 eq54188
  have eq54211 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op (M.op X1 (M.op X2 (M.op x y))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54201 X0 X1 X2
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq54201
    | exact resolve eq54201 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54201
  have eq116779 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq74 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116780 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq116779
    | exact resolve eq116779 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116779
  have eq116791 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq116780
       have r₂ := eq28
       grind)
    | exact resolve eq116780 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116780
  have eq116793 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq116791
    | exact resolve eq116791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116791
  have eq116812 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq116793 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq116793
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq116793
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq116793
       grind)
    | exact resolve eq12 eq116793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116793
  have eq116886 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq116812
  have eq116928 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq116886
       have r₂ := eq27
       grind)
    | exact resolve eq116886 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116886
  have eq116993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq116928 eq74
    | exact resolve eq74 eq116928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116928
  have eq117002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq116993
  have eq117005 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq117002
       have r₂ := eq28
       grind)
    | exact resolve eq117002 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117002
  have eq117255 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq117005
  have eq117581 : (τ (σ x)) = (k x y) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq117255 eq61
    | exact resolve eq61 eq117255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq117582 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq117255 eq74
    | exact resolve eq74 eq117255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq117255
  have eq117592 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq117582
  have eq117601 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq117581
    | exact resolve eq117581 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117581
  have eq117918 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 (M.op x (M.op x y))) X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq37562 X0 x X1 y
       have i₂ := eq117592
       grind)
    | exact superpose eq117592 eq37562
    | exact resolve eq37562 eq117592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117961 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq54211 eq117918
    | exact resolve eq117918 eq54211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117918
  have eq120201 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 (M.op x (M.op x y))) X0) ∨ y = (M.op x x) ∨ x = (k x y) := by
    intro X0 X1
    first
    | (have i₁ := eq37562 X0 x X1 y
       have i₂ := eq117601
       grind)
    | exact superpose eq117601 eq37562
    | exact resolve eq37562 eq117601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37562
  have eq120244 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ y = (M.op x x) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq54211 eq120201
    | exact resolve eq120201 eq54211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54211 eq120201
  have eq120549 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq117592
       have i₂ := eq117961 x
       grind)
    | exact superpose eq117961 eq117592
    | exact resolve eq117592 eq117961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117592 eq117961
  have eq121008 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by grind
  clear eq120549
  have eq121452 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq121008
       grind)
    | exact superpose eq121008 eq53
    | exact resolve eq53 eq121008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121008
  have eq121964 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq121452 eq8840
    | exact resolve eq8840 eq121452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121452
  have eq122100 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq50 eq121964
    | exact resolve eq121964 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121964
  have eq122130 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq429
       have i₂ := eq122100
       grind)
    | exact superpose eq122100 eq429
    | exact resolve eq429 eq122100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122236 : (M.op x y) = (M.op x (M.op y (M.op y (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14861 x x
       have i₂ := eq122100
       grind)
    | exact superpose eq122100 eq14861
    | exact resolve eq14861 eq122100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122100
  have eq122287 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq122130
  have eq122314 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq10479 eq122236
    | exact resolve eq122236 eq10479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122236
  have eq122391 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq122287
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq122287
    | exact resolve eq122287 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122287
  have eq122730 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq430
       have i₂ := eq122314
       grind)
    | exact superpose eq122314 eq430
    | exact resolve eq430 eq122314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122314
  have eq122971 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq21 eq122730
    | exact resolve eq122730 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122730
  have eq124232 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq122391
       have i₂ := eq84 sF2
       grind)
    | exact superpose eq84 eq122391
    | (have j1 := eq84 (σ x)
       grind)
    | exact resolve eq122391 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258894 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq124232 eq1415
    | exact resolve eq1415 eq124232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124232
  have eq259189 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq258894
    | exact resolve eq258894 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258894
  have eq295908 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ x = (k x y) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq117601
       have i₂ := eq120244 x
       grind)
    | exact superpose eq120244 eq117601
    | exact resolve eq117601 eq120244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117601 eq120244
  have eq296614 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ x = (k x y) := by grind
  clear eq295908
  have eq297212 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq296614
       grind)
    | exact superpose eq296614 eq53
    | exact resolve eq53 eq296614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq296614
  have eq301046 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ y = (M.op x x) ∨ x = (k x y) := by
    intro X0
    first
    | exact superpose eq297212 eq8840
    | exact resolve eq8840 eq297212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8840 eq297212
  have eq301225 : y = (M.op x x) ∨ x = y ∨ x = (k x y) := by
    first
    | exact superpose eq50 eq301046
    | exact resolve eq301046 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq301046
  have eq301298 : x = (k x y) ∨ x = y ∨ x = (k x y) := by grind
  clear eq301225
  have eq301482 : x = (k x y) ∨ x = y := by grind
  clear eq301298
  have eq302363 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq45
       have i₂ := eq301482
       grind)
    | exact superpose eq301482 eq45
    | exact resolve eq45 eq301482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq302378 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq301482
       grind)
    | exact superpose eq301482 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq301482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302380 : x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq302378
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq302378
    | exact resolve eq302378 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302378
  have eq302393 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq302363
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq302363
    | exact resolve eq302363 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302363
  have eq302395 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq302380
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq302380
    | exact resolve eq302380 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302380
  have eq302416 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq302393 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq302393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302420 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq302416
    | exact resolve eq302416 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302416
  have eq302431 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq27 eq302420
    | exact resolve eq302420 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302420
  have eq337281 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq302395
       grind)
    | exact superpose eq302395 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq302395
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq302395
       grind)
    | exact resolve eq12 eq302395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302395
  have eq337370 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq337281
  have eq337457 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq337370
       have r₂ := eq19
       grind)
    | exact resolve eq337370 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337370
  have eq337565 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq302431 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq302431
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq302431
       grind)
    | exact resolve eq12 eq302431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302431
  have eq337654 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq337565
  have eq337703 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq337654
       have r₂ := eq27
       grind)
    | exact resolve eq337654 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337654
  have eq346517 : x = (M.op x y) ∨ x = y ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq301482
       have i₂ := eq337457
       grind)
    | exact superpose eq337457 eq301482
    | exact resolve eq301482 eq337457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301482 eq337457
  have eq346566 : y = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq346517
  have eq346630 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1415 x
       have i₂ := eq346566
       grind)
    | exact superpose eq346566 eq1415
    | exact resolve eq1415 eq346566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346761 : (M.op x y) = (M.op x (M.op y (M.op y (M.op x y)))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14861 x x
       have i₂ := eq346566
       grind)
    | exact superpose eq346566 eq14861
    | exact resolve eq14861 eq346566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14861 eq346566
  have eq346880 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq10479 eq346761
    | exact resolve eq346761 eq10479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10479 eq346761
  have eq346970 : x = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq346630
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq346630
    | exact resolve eq346630 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346630
  have eq347492 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq430
       have i₂ := eq346880
       grind)
    | exact superpose eq346880 eq430
    | exact resolve eq430 eq346880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346880
  have eq347848 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq347492
    | exact resolve eq347492 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347492
  have eq501810 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq337703 eq302393
    | exact resolve eq302393 eq337703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302393 eq337703
  have eq501875 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq501810
  have eq501914 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq501875 eq1415
    | exact resolve eq1415 eq501875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq502076 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq501875 eq14862
    | exact resolve eq14862 eq501875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14862 eq501875
  have eq502193 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10640 eq502076
    | exact resolve eq502076 eq10640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10640 eq502076
  have eq502302 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq501914
    | exact resolve eq501914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501914
  have eq502934 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq502193 eq12
    | exact resolve eq12 eq502193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502193
  have eq503042 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq502934
  have eq547855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq503042 eq122971
    | exact resolve eq122971 eq503042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122971
  have eq547859 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq503042 eq347848
    | exact resolve eq347848 eq503042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347848
  have eq547868 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq547859
  have eq547869 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq547855
  have eq547872 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq547868
       have r₂ := eq28
       grind)
    | exact resolve eq547868 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547868
  have eq547874 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq547869
       have r₂ := eq28
       grind)
    | exact resolve eq547869 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547869
  have eq654104 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq547872 eq502302
    | exact resolve eq502302 eq547872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654164 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq547872
  have eq654216 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq654104
  have eq654295 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq654216
    | exact resolve eq654216 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654216
  have eq654296 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq654295
  have eq654570 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq547874 eq502302
    | exact resolve eq502302 eq547874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654630 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq547874
  have eq654682 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq654570
  have eq654764 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq654682
    | exact resolve eq654682 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654682
  have eq654765 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq654764
  have eq664790 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq654296
       have r₂ := eq654164
       grind)
    | exact resolve eq654296 eq654164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654164 eq654296
  have eq664793 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq664790 eq28
    | exact resolve eq28 eq664790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664790
  have eq666232 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq654765
       have r₂ := eq654630
       grind)
    | exact resolve eq654765 eq654630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654630 eq654765
  have eq666402 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq666232 eq259189
    | exact resolve eq259189 eq666232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259189 eq666232
  have eq666463 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq666402
  have eq666578 : (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq666463
  have eq668093 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq666578 eq122391
    | exact resolve eq122391 eq666578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122391 eq666578
  have eq668136 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq668093
  have eq668168 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq668136 eq30
    | exact resolve eq30 eq668136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq668136
  have eq668923 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq668168
    | exact resolve eq668168 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq668168
  have eq668924 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq668923
  have eq669246 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq668924 eq664793
    | (have r₁ := eq664793
       have r₂ := eq668924
       grind)
    | exact resolve eq664793 eq668924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664793 eq668924
  have eq669249 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq669246
  have eq669250 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq669249
  have eq670058 : x = (M.op x y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq669250 eq346970
    | exact resolve eq346970 eq669250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346970 eq669250
  have eq670320 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq670058
  have eq670482 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq670320
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq670320
    | exact resolve eq670320 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670320
  have eq670483 : x = (M.op x y) ∨ x = y := by grind
  clear eq670482
  have eq670696 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq670483 eq21
    | exact resolve eq21 eq670483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670746 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op y y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq670483 eq205
    | exact resolve eq205 eq670483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq670849 : (M.op x x) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq670483 eq3933
    | exact resolve eq3933 eq670483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3933
  have eq671483 : y = (M.op y (M.op y (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq670746 x
       have i₂ := eq11294 y x x
       grind)
    | exact superpose eq11294 eq670746
    | exact resolve eq670746 eq11294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11294 eq670746
  have eq671530 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq670696
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq670696
    | exact resolve eq670696 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670696
  have eq671536 : y = (M.op y (M.op y (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq671483
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq671483
    | exact resolve eq671483 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671483
  have eq680498 : y = (M.op y (M.op y x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq670483 eq671536
    | exact resolve eq671536 eq670483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670483 eq671536
  have eq680733 : y = (M.op y (M.op y x)) ∨ x = y := by grind
  clear eq680498
  have eq697151 : y = (M.op y (M.op x x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq680733
       have i₂ := eq670849
       grind)
    | exact superpose eq670849 eq680733
    | exact resolve eq680733 eq670849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670849 eq680733
  have eq697352 : y = (M.op y (M.op x x)) ∨ x = y := by grind
  clear eq697151
  have eq697482 : y = (M.op x (M.op (M.op x y) x)) ∨ x = y := by
    first
    | (have i₁ := eq697352
       have i₂ := eq7721 x
       grind)
    | exact superpose eq7721 eq697352
    | exact resolve eq697352 eq7721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7721 eq697352
  have eq718693 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq697482 eq14
    | exact resolve eq14 eq697482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697482
  have eq719061 : x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq7634 eq718693
    | exact resolve eq718693 eq7634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7634 eq718693
  have eq719225 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq430
       have i₂ := eq719061
       grind)
    | exact superpose eq719061 eq430
    | exact resolve eq430 eq719061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq719061
  have eq719620 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq719225
  have eq719720 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq719620
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq719620
    | exact resolve eq719620 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719620
  have eq719872 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq719720 eq503042
    | exact resolve eq503042 eq719720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503042 eq719720
  have eq719883 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq719872
  have eq720108 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq719883 eq502302
    | exact resolve eq502302 eq719883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502302
  have eq720201 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq719883
  have eq720285 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq720108
  have eq720368 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq720285
    | exact resolve eq720285 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720285
  have eq720369 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq720368
  have eq720446 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq720369
       have r₂ := eq720201
       grind)
    | exact resolve eq720369 eq720201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720201 eq720369
  have eq720450 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq720446 eq28
    | exact resolve eq28 eq720446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720446
  have eq720776 : x = y := by
    first
    | (have r₁ := eq720450
       have r₂ := eq671530
       grind)
    | exact resolve eq720450 eq671530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671530 eq720450
  have eq720783 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq720776
       grind)
    | exact superpose eq720776 eq19
    | exact resolve eq19 eq720776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq720784 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq720776
       grind)
    | exact superpose eq720776 eq25
    | exact resolve eq25 eq720776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq720776
  have eq721320 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq720784
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq720784
    | exact resolve eq720784 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720784
  have eq721348 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq721320 eq27
    | exact resolve eq27 eq721320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq721320
  have eq722078 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq429
       have i₂ := eq720783
       grind)
    | exact superpose eq720783 eq429
    | exact resolve eq429 eq720783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq722148 : x = (k x (M.op x y)) := by grind
  clear eq720783
  have eq722570 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq722078
    | exact resolve eq722078 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722078
  have eq722827 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  have eq748229 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq722570 eq84
    | (have j0 := eq84 (σ x)
       grind)
    | exact resolve eq84 eq722570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq748250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq721348 eq748229
    | exact resolve eq748229 eq721348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748229
  have eq748262 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq748250
       have r₂ := eq28
       grind)
    | exact resolve eq748250 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748250
  have eq748267 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq721348 eq748262
    | exact resolve eq748262 eq721348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748262
  have eq748274 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq748267 eq28
    | exact resolve eq28 eq748267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748502 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq748267 eq722827
    | exact resolve eq722827 eq748267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722827 eq748267
  have eq749039 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq748502 eq722570
    | exact resolve eq722570 eq748502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722570 eq748502
  have eq749055 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq749039
  have eq749076 : x = (M.op x y) := by
    first
    | (have r₁ := eq749055
       have r₂ := eq748274
       grind)
    | exact resolve eq749055 eq748274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748274 eq749055
  have eq749118 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq749076 eq21
    | exact resolve eq21 eq749076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq749658 : x = (k x x) := by
    first
    | exact superpose eq749076 eq722148
    | exact resolve eq722148 eq749076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722148 eq749076
  have eq750029 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq749118
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq749118
    | exact resolve eq749118 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749118
  have eq751135 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4659 x
       have i₂ := eq749658
       grind)
    | exact superpose eq749658 eq4659
    | (have j0 := eq4659 x
       grind)
    | exact resolve eq4659 eq749658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4659 eq749658
  have eq751140 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq751135
  have eq751158 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq751140
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq751140
    | exact resolve eq751140 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq751140
  have eq751181 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq721348 eq751158
    | exact resolve eq751158 eq721348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721348 eq751158
  have eq751202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq750029 eq751181
    | exact resolve eq751181 eq750029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750029 eq751181
  have eq751221 : False := by grind
  exact eq751221

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_pyy_x_pxy_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  clear eq36
  have eq47 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
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
  have eq48 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq78 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq86 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
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
  have eq112 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq121 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq152 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq112 eq16
    | exact resolve eq16 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq207 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op X0 (M.op (σ y) X0)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq48 eq14
    | exact resolve eq14 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq53 X0 X2
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq80 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq80
    | (have j0 := eq80 (σ X0)
       grind)
    | exact resolve eq80 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq80 x
       grind)
    | exact superpose eq80 eq44
    | (have j1 := eq80 x
       grind)
    | exact resolve eq44 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq423 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq80 y
       grind)
    | exact superpose eq80 eq86
    | (have j1 := eq80 y
       grind)
    | exact resolve eq86 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq425 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq152
       have i₂ := eq80 sF1
       grind)
    | exact superpose eq80 eq152
    | (have j1 := eq80 (σ (M.op x y))
       grind)
    | exact resolve eq152 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq521 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq522 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X1 X0 (M.op X0 X1)
       have i₂ := eq53 (M.op X0 X1) X1
       grind)
    | exact superpose eq53 eq49
    | exact resolve eq49 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X1 X2
       have i₂ := eq49 X2 X3 X0
       grind)
    | exact superpose eq49 eq14
    | exact resolve eq14 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq49 y X1 X0
       grind)
    | exact superpose eq49 eq47
    | exact resolve eq47 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq49 sF3 x x
       grind)
    | exact superpose eq49 eq48
    | exact resolve eq48 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq774 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq216 sF4
       have i₂ := eq53 sF4 sF3
       grind)
    | exact superpose eq53 eq216
    | exact resolve eq216 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq801 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq802 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op (M.op y (M.op x y)) y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq814 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq53 (M.op (M.op X0 (M.op X0 X0)) X0) x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq898 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq66 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq66 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq66 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq66 X0 X0
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq906 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq898 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq909 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq906 X0 X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq906
    | (have j0 := eq906 X0 X1
       grind)
    | exact resolve eq906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq1380 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq227 X0 x x
       grind)
    | exact superpose eq227 eq53
    | exact resolve eq53 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1382 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1380 X0
       have i₂ := eq227 X0 X0 X0
       grind)
    | exact superpose eq227 eq1380
    | exact resolve eq1380 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq3662 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq801 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1382 sF0
       grind)
    | exact superpose eq1382 eq801
    | exact resolve eq801 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3685 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq3662
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq3662
    | exact resolve eq3662 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3662
  have eq3687 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3685 eq801
    | exact resolve eq801 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801 eq3685
  have eq3707 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3687 eq14
    | exact resolve eq14 eq3687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3736 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq802 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1382 sF4
       grind)
    | exact superpose eq1382 eq802
    | exact resolve eq802 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3759 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3736
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3736
    | exact resolve eq3736 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3736
  have eq3775 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3759 eq802
    | exact resolve eq802 eq3759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3848 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3707 eq47
    | exact resolve eq47 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq3707
  have eq3869 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq3848 eq3687
    | exact resolve eq3687 eq3848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3687 eq3848
  have eq3979 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | exact superpose eq774 eq207
    | exact resolve eq207 eq774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq4011 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3979 X0
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3979
    | exact resolve eq3979 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3979
  have eq4012 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4011 x
       have i₂ := eq53 sF4 x
       grind)
    | exact superpose eq53 eq4011
    | exact resolve eq4011 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4011
  have eq4013 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3759 eq4012
    | exact resolve eq4012 eq3759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3759 eq4012
  have eq4014 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4013 eq3775
    | exact resolve eq3775 eq4013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4444 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0) (σ X0)
       have i₂ := eq418 X0
       grind)
    | exact superpose eq418 eq53
    | (have j1 := eq418 X0
       grind)
    | exact resolve eq53 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq5678 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq521 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq227 X0 x X2
       grind)
    | exact superpose eq227 eq521
    | exact resolve eq521 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq5771 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq5678 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq5678
    | exact resolve eq5678 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5678
  have eq5782 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5771 X0 x
       have i₂ := eq53 X0 x
       grind)
    | exact superpose eq53 eq5771
    | exact resolve eq5771 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5771
  have eq6644 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq814 X0 X1 X2 X3
       have i₂ := eq5782 X0
       grind)
    | exact superpose eq5782 eq814
    | exact resolve eq814 eq5782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq6747 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6644 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq227 X0 x x
       grind)
    | exact superpose eq227 eq6644
    | exact resolve eq6644 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6644
  have eq6959 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6747 X0 X1 X2
       have i₂ := eq227 X0 X0 X0
       grind)
    | exact superpose eq227 eq6747
    | exact resolve eq6747 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6747
  have eq6994 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6959 X0 X1 X2
       have i₂ := eq5782 X0
       grind)
    | exact superpose eq5782 eq6959
    | exact resolve eq6959 eq5782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5782 eq6959
  have eq7052 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq6994 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq6994
    | (have j0 := eq6994 y X0 x
       grind)
    | exact resolve eq6994 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7064 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq6994
    | (have j0 := eq6994 (σ y) X0 (σ x)
       grind)
    | exact resolve eq6994 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7080 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6994 (M.op X1 X0) (M.op x X1) X0
       have i₂ := eq14 X0 x X1
       grind)
    | exact superpose eq14 eq6994
    | exact resolve eq6994 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7141 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq802 X0
       have i₂ := eq6994 X0 X0 sF4
       grind)
    | exact superpose eq6994 eq802
    | exact resolve eq802 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq802
  have eq7336 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq826 X0
       have i₂ := eq6994 X0 X0 X0
       grind)
    | exact superpose eq6994 eq826
    | exact resolve eq826 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq7737 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 X1
       have i₂ := eq6994 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq6994 eq529
    | exact resolve eq529 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq7909 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 y x X0
       have i₂ := eq7737 X0 x
       grind)
    | exact superpose eq7737 eq49
    | exact resolve eq49 eq7737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7737
  have eq8039 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq7909 (M.op X0 X0)
       have i₂ := eq7336 X0
       grind)
    | exact superpose eq7336 eq7909
    | exact resolve eq7909 eq7336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7336
  have eq8042 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq7909 (M.op X0 (M.op X0 X0))
       have i₂ := eq227 X0 X0 X0
       grind)
    | exact superpose eq227 eq7909
    | exact resolve eq7909 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8162 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1382 X0
       have i₂ := eq8042 X0
       grind)
    | exact superpose eq8042 eq1382
    | exact resolve eq1382 eq8042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq8168 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq8042 X0
       grind)
    | exact superpose eq8042 eq14
    | exact resolve eq14 eq8042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8182 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7141 sF4
       have i₂ := eq8042 sF4
       grind)
    | exact superpose eq8042 eq7141
    | exact resolve eq7141 eq8042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7141
  have eq8227 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq774
       have i₂ := eq8042 sF4
       grind)
    | exact superpose eq8042 eq774
    | exact resolve eq774 eq8042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq8246 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq8042 eq14
    | exact resolve eq14 eq8042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8042
  have eq8269 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8246 X0 X1
       have i₂ := eq14 X0 sF0 X0
       grind)
    | exact superpose eq14 eq8246
    | exact resolve eq8246 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8246
  have eq8305 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq4013 eq8182
    | exact resolve eq8182 eq4013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4013 eq8182
  have eq8381 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq6994 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq6994 eq530
    | exact resolve eq530 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq8646 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq8381 eq49
    | exact resolve eq49 eq8381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8381
  have eq8793 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq8646 (M.op X0 (M.op X0 X0))
       have i₂ := eq227 X0 X0 X0
       grind)
    | exact superpose eq227 eq8646
    | exact resolve eq8646 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq8646
  have eq9079 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op x y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq812 X0 X1 X2
       have i₂ := eq8269 (M.op y sF0) (M.op y sF0)
       grind)
    | exact superpose eq8269 eq812
    | exact resolve eq812 eq8269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq8269
  have eq9080 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3869 eq9079
    | exact resolve eq9079 eq3869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3869 eq9079
  have eq9081 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7052 eq9080
    | exact resolve eq9080 eq7052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7052 eq9080
  have eq9179 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq8793 eq14
    | exact resolve eq14 eq8793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8793
  have eq9202 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9179 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq9179
    | exact resolve eq9179 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9179
  have eq9699 : (M.op y y) = (M.op x (M.op y (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq9081 (M.op x (M.op x x)) x x
       have i₂ := eq49 x x x
       grind)
    | exact superpose eq49 eq9081
    | exact resolve eq9081 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9081
  have eq9820 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq9202 eq813
    | exact resolve eq813 eq9202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq9202
  have eq9821 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4014 eq9820
    | exact resolve eq9820 eq4014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014 eq9820
  have eq9822 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq7064 eq9821
    | exact resolve eq9821 eq7064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7064 eq9821
  have eq9850 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq9822 (M.op x (M.op x x)) x sF2
       have i₂ := eq49 x x sF2
       grind)
    | exact superpose eq49 eq9822
    | exact resolve eq9822 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9822
  have eq11390 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq8305 eq9850
    | exact resolve eq9850 eq8305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8305
  have eq12326 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq527 X0 X1 X2 X3
       have i₂ := eq6994 X0 X0 (M.op X2 (M.op X3 X2))
       grind)
    | exact superpose eq6994 eq527
    | exact resolve eq527 eq6994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq6994
  have eq12712 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 x X2
       have i₂ := eq12326 X2 X0 X1 x
       grind)
    | exact superpose eq12326 eq49
    | exact resolve eq49 eq12326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq12326
  have eq26524 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq909 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq55510 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) = (M.op y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq8039 (M.op X0 sF0)
       have i₂ := eq12712 X0 sF0 (M.op X0 sF0)
       grind)
    | exact superpose eq12712 eq8039
    | exact resolve eq8039 eq12712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8039 eq12712
  have eq55626 : ∀ X0 : G, (M.op y (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq55510 x
       have i₂ := eq7080 sF0 x
       grind)
    | exact superpose eq7080 eq55510
    | exact resolve eq55510 eq7080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7080 eq55510
  have eq55914 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X1 X0) (M.op y (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq55626 eq14
    | exact resolve eq14 eq55626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55626
  have eq59833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59834 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq59833
    | exact resolve eq59833 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59833
  have eq59845 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq59834
       have r₂ := eq28
       grind)
    | exact resolve eq59834 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59834
  have eq59847 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq59845
    | exact resolve eq59845 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59845
  have eq59850 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59847 eq78
    | (have r₁ := eq78
       have r₂ := eq59847
       grind)
    | exact resolve eq78 eq59847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq59871 : (σ x) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59847 eq7909
    | exact resolve eq7909 eq59847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7909
  have eq59908 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59847 eq522
    | exact resolve eq522 eq59847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522 eq59847
  have eq59942 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq59850
  have eq59943 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq59942
  have eq59959 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3775 eq59908
    | exact resolve eq59908 eq3775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775 eq59908
  have eq59991 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq9850 eq59959
    | exact resolve eq59959 eq9850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9850 eq59959
  have eq60457 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq59991
  have eq61053 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59871 eq8227
    | exact resolve eq8227 eq59871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8227 eq59871
  have eq61723 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq59943 eq98
    | exact resolve eq98 eq59943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59943
  have eq61732 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq61723
  have eq61805 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq61732 eq53
    | exact resolve eq53 eq61732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61732
  have eq61860 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq61805
    | exact resolve eq61805 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61805
  have eq62166 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq61860 eq61053
    | exact resolve eq61053 eq61860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61053 eq61860
  have eq62217 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62166
  have eq62241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq62217
       have r₂ := eq60457
       grind)
    | exact resolve eq62217 eq60457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60457 eq62217
  have eq62244 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq62241
       have r₂ := eq28
       grind)
    | exact resolve eq62241 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62241
  have eq62270 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  have eq62315 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq62244 eq53
    | exact resolve eq53 eq62244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62244
  have eq62370 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq62315
    | exact resolve eq62315 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62315
  have eq62450 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq62370
       grind)
    | exact superpose eq62370 eq53
    | exact resolve eq53 eq62370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62370
  have eq62593 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq62450 eq8168
    | exact resolve eq8168 eq62450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62450
  have eq62675 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq50 eq62593
    | exact resolve eq62593 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62593
  have eq62704 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq423
       have i₂ := eq62675
       grind)
    | exact superpose eq62675 eq423
    | exact resolve eq423 eq62675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62765 : x ≠ x ∨ x = y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq62675
       grind)
    | exact superpose eq62675 eq12
    | exact resolve eq12 eq62675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62771 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq62675
       grind)
    | exact superpose eq62675 eq53
    | exact resolve eq53 eq62675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62675
  have eq62810 : x ≠ x ∨ x = y ∨ x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62765
  have eq62811 : x = (k y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62810
  have eq62812 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62704
  have eq62828 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq62771
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq62771
    | exact resolve eq62771 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62771
  have eq62849 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62812
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq62812
    | exact resolve eq62812 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62812
  have eq62857 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq62828 eq28
    | exact resolve eq28 eq62828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62908 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq62828 eq11390
    | exact resolve eq11390 eq62828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11390 eq62828
  have eq62949 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8162 eq62908
    | exact resolve eq62908 eq8162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8162 eq62908
  have eq80482 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq62270 eq98
    | exact resolve eq98 eq62270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq62270
  have eq80493 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq80482
  have eq80574 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq80493
       grind)
    | exact superpose eq80493 eq53
    | exact resolve eq53 eq80493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80493
  have eq81072 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq80574 eq8168
    | exact resolve eq8168 eq80574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8168 eq80574
  have eq81161 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq50 eq81072
    | exact resolve eq81072 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq81072
  have eq81194 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq423
       have i₂ := eq81161
       grind)
    | exact superpose eq81161 eq423
    | exact resolve eq423 eq81161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81279 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq81161
       grind)
    | exact superpose eq81161 eq53
    | exact resolve eq53 eq81161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81320 : (M.op x y) = (M.op x (M.op y (M.op y (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq55914 y y
       have i₂ := eq81161
       grind)
    | exact superpose eq81161 eq55914
    | exact resolve eq55914 eq81161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55914 eq81161
  have eq81324 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq81194
  have eq81326 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9699 eq81320
    | exact resolve eq81320 eq9699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9699 eq81320
  have eq81345 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq81279
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq81279
    | exact resolve eq81279 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81279
  have eq81368 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq81324
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq81324
    | exact resolve eq81324 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81324
  have eq81599 : (k y (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq81345 eq121
    | exact resolve eq121 eq81345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq81737 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq81345 eq62949
    | exact resolve eq62949 eq81345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62949 eq81345
  have eq81778 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq81737
  have eq81849 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq152 eq81599
    | exact resolve eq81599 eq152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq81599
  have eq82383 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq423
       have i₂ := eq81326
       grind)
    | exact superpose eq81326 eq423
    | exact resolve eq423 eq81326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq81326
  have eq82573 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq82383
    | exact resolve eq82383 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82383
  have eq82883 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq81778 eq425
    | exact resolve eq425 eq81778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq81778
  have eq83013 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq82883
       have r₂ := eq62857
       grind)
    | exact resolve eq82883 eq62857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62857 eq82883
  have eq83017 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq83013
    | exact resolve eq83013 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq83013
  have eq88818 : x = (k y (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq81849 eq83017
    | exact resolve eq83017 eq81849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81849 eq83017
  have eq88822 : x = (k y (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq88818
  have eq112839 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq82573 eq81368
    | exact resolve eq81368 eq82573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81368 eq82573
  have eq112856 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq112839
  have eq112880 : y = (τ (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq112856 eq30
    | exact resolve eq30 eq112856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112856
  have eq113214 : y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq112880
    | exact resolve eq112880 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112880
  have eq113215 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq113214
  have eq372923 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4444 y
       have i₂ := eq62811
       grind)
    | exact superpose eq62811 eq4444
    | (have j0 := eq4444 y
       grind)
    | exact resolve eq4444 eq62811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4444 eq62811
  have eq373355 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq372923
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq372923
    | exact resolve eq372923 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372923
  have eq373396 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq373355
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq373355
    | exact resolve eq373355 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373355
  have eq373418 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq373396
    | exact resolve eq373396 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373396
  have eq373419 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq373418
  have eq373426 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq373419
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq373419
    | exact resolve eq373419 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373419
  have eq373493 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq373426
  have eq373889 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq373493 eq62849
    | exact resolve eq62849 eq373493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62849 eq373493
  have eq373950 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq373889
  have eq373977 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq373950 eq28
    | exact resolve eq28 eq373950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373950
  have eq374977 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq113215 eq373977
    | (have r₁ := eq373977
       have r₂ := eq113215
       grind)
    | exact resolve eq373977 eq113215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113215 eq373977
  have eq374978 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq374977
  have eq374979 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq374978
  have eq374981 : y = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq374979 eq30
    | exact resolve eq30 eq374979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq374979
  have eq375579 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq374981
    | exact resolve eq374981 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq374981
  have eq375580 : y = (M.op x y) ∨ x = y := by grind
  clear eq375579
  have eq376140 : x = (k y y) ∨ x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq375580 eq88822
    | exact resolve eq88822 eq375580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88822
  have eq376314 : x = (k y y) ∨ x = y := by grind
  clear eq376140
  have eq377468 : y = (M.op y y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq376314
       have i₂ := eq80 y
       grind)
    | exact superpose eq80 eq376314
    | (have j1 := eq80 y
       grind)
    | exact resolve eq376314 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2013109 : y = (k y y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq377468
  have eq2050379 : x = y ∨ x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq376314
       have i₂ := eq2013109
       grind)
    | exact superpose eq2013109 eq376314
    | exact resolve eq376314 eq2013109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376314 eq2013109
  have eq2050476 : x = (M.op y y) ∨ x = y := by grind
  clear eq2050379
  have eq2050914 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq53 y y
       have i₂ := eq2050476
       grind)
    | exact superpose eq2050476 eq53
    | exact resolve eq53 eq2050476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq2050476
  have eq2051238 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2050914
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2050914
    | exact resolve eq2050914 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050914
  have eq2051931 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2051238 eq375580
    | exact resolve eq375580 eq2051238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375580 eq2051238
  have eq2052706 : x = y := by grind
  clear eq2051931
  have eq2053045 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2052706
       grind)
    | exact superpose eq2052706 eq19
    | exact resolve eq19 eq2052706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2053046 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2052706
       grind)
    | exact superpose eq2052706 eq25
    | exact resolve eq25 eq2052706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2052706
  have eq2053690 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2053046
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2053046
    | exact resolve eq2053046 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053046
  have eq2057292 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2053690 eq27
    | exact resolve eq27 eq2053690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2053690
  have eq2058731 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq422
       have i₂ := eq2053045
       grind)
    | exact superpose eq2053045 eq422
    | exact resolve eq422 eq2053045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq2058786 : x = (k x (M.op x y)) := by grind
  clear eq2053045
  have eq2059412 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq2058731
    | exact resolve eq2058731 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058731
  have eq2059911 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  have eq2110563 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2059412 eq80
    | (have j0 := eq80 (σ x)
       grind)
    | exact resolve eq80 eq2059412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq2110600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2057292 eq2110563
    | exact resolve eq2110563 eq2057292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110563
  have eq2110613 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2110600
       have r₂ := eq28
       grind)
    | exact resolve eq2110600 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110600
  have eq2110619 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2057292 eq2110613
    | exact resolve eq2110613 eq2057292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110613
  have eq2112862 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2110619 eq28
    | exact resolve eq28 eq2110619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2113650 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2110619 eq2059911
    | exact resolve eq2059911 eq2110619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059911 eq2110619
  have eq2116471 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2113650 eq2059412
    | exact resolve eq2059412 eq2113650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059412 eq2113650
  have eq2116514 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2116471
  have eq2116528 : x = (M.op x y) := by
    first
    | (have r₁ := eq2116514
       have r₂ := eq2112862
       grind)
    | exact resolve eq2116514 eq2112862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112862 eq2116514
  have eq2116557 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2116528 eq21
    | exact resolve eq21 eq2116528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq2117451 : x = (k x x) := by
    first
    | exact superpose eq2116528 eq2058786
    | exact resolve eq2058786 eq2116528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058786 eq2116528
  have eq2117851 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2116557
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2116557
    | exact resolve eq2116557 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2116557
  have eq2122256 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26524 x x
       have i₂ := eq2117451
       grind)
    | exact superpose eq2117451 eq26524
    | (have j0 := eq26524 x x
       grind)
    | exact resolve eq26524 eq2117451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26524 eq2117451
  have eq2122259 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2122256
  have eq2122260 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq2122259
  have eq2122273 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2122260
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2122260
    | exact resolve eq2122260 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2122260
  have eq2122321 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2057292 eq2122273
    | exact resolve eq2122273 eq2057292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057292 eq2122273
  have eq2122366 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2117851 eq2122321
    | exact resolve eq2122321 eq2117851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2117851 eq2122321
  have eq2122406 : False := by grind
  exact eq2122406

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pxy_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 (M.op (M.op X0 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op x X2) (M.op X0 (M.op X2 X0))
       have i₂ := eq14 X0 x X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
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
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X0
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
  have eq71 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq79 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq88 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq92 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq100 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq92
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq103
    | exact resolve eq103 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq106 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq16
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq106
  have eq130 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
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
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq149 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq132
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq132
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq149
  have eq214 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq50 (M.op y y)
       have i₂ := eq14 y y y
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq51 (M.op sF3 sF3)
       have i₂ := eq14 sF3 sF3 sF3
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X0) X0
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq13
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq56 X0 X0
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 (M.op X2 X0)
       have i₂ := eq56 X0 X2
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 X1) X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 (M.op X0 (M.op (M.op X2 X1) X0))
       have i₂ := eq14 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq417 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1)))) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1)))) X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X2 (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1)))) X0))
       have i₂ := eq52 (M.op X1 (M.op X2 X1)) X3 X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) X1 X2
       have i₂ := eq52 X2 X3 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X0 (M.op (M.op y (M.op X1 y)) X0))
       have i₂ := eq52 y X1 X0
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op x (M.op (M.op sF3 (M.op x sF3)) x))
       have i₂ := eq52 sF3 x x
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op (M.op X0 (M.op (M.op x y) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq705 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) X0)) := by
    intro X0
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op (M.op y (M.op x y)) y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq716 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq55
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 (M.op X1 X0)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1165 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (M.op X0 (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0))
       have i₂ := eq252 X0 x x
       grind)
    | exact superpose eq252 eq56
    | exact resolve eq56 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1169 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1165 X0
       have i₂ := eq252 X0 X0 X0
       grind)
    | exact superpose eq252 eq1165
    | exact resolve eq1165 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1165
  have eq3459 : (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) = (M.op y (M.op (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
    first
    | (have i₁ := eq704 (M.op sF0 (M.op sF0 sF0))
       have i₂ := eq1169 sF0
       grind)
    | exact superpose eq1169 eq704
    | exact resolve eq704 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3484 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq3459
       have i₂ := eq14 sF0 (M.op sF0 (M.op sF0 sF0)) sF0
       grind)
    | exact superpose eq14 eq3459
    | exact resolve eq3459 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3459
  have eq3486 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq3484 eq704
    | exact resolve eq704 eq3484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3484
  have eq3510 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op y (M.op y (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq3486 eq14
    | exact resolve eq14 eq3486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3542 : (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))))) := by
    first
    | (have i₁ := eq705 (M.op sF4 (M.op sF4 sF4))
       have i₂ := eq1169 sF4
       grind)
    | exact superpose eq1169 eq705
    | exact resolve eq705 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3567 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3542
       have i₂ := eq14 sF4 (M.op sF4 (M.op sF4 sF4)) sF4
       grind)
    | exact superpose eq14 eq3542
    | exact resolve eq3542 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3542
  have eq3589 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3567 eq705
    | exact resolve eq705 eq3567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3567
  have eq3613 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq3589 eq14
    | exact resolve eq14 eq3589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3678 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3510 eq50
    | exact resolve eq50 eq3510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3510
  have eq3723 : (M.op y (M.op y (M.op x y))) = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq3678 eq3486
    | exact resolve eq3486 eq3678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486
  have eq3804 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq251 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq3876 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3613 eq51
    | exact resolve eq51 eq3613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3613
  have eq3901 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3876 eq3589
    | exact resolve eq3589 eq3876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589
  have eq5349 : ∀ X0 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X2 X0) (M.op (M.op (M.op X0 (M.op X0 X0)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X2
    first
    | (have i₁ := eq415 (M.op X0 (M.op X0 X0)) (M.op X2 X0) x
       have i₂ := eq252 X0 x X2
       grind)
    | exact superpose eq252 eq415
    | exact resolve eq415 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq5447 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0 X2
    first
    | (have i₁ := eq5349 X0 X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X0)) X0
       grind)
    | exact superpose eq14 eq5349
    | exact resolve eq5349 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349
  have eq5458 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5447 X0 x
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq5447
    | exact resolve eq5447 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5447
  have eq6556 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X3 (M.op X1 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq717 X0 X1 X2 X3
       have i₂ := eq5458 X0
       grind)
    | exact superpose eq5458 eq717
    | exact resolve eq717 eq5458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq6654 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6556 (M.op X0 (M.op X0 X0)) (M.op x (M.op x X0)) X1 X2
       have i₂ := eq252 X0 x x
       grind)
    | exact superpose eq252 eq6556
    | exact resolve eq6556 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6556
  have eq6870 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6654 X0 X1 X2
       have i₂ := eq252 X0 X0 X0
       grind)
    | exact superpose eq252 eq6654
    | exact resolve eq6654 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6654
  have eq6905 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6870 X0 X1 X2
       have i₂ := eq5458 X0
       grind)
    | exact superpose eq5458 eq6870
    | exact resolve eq6870 eq5458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5458 eq6870
  have eq6960 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq6905 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6905
    | (have j0 := eq6905 y X0 x
       grind)
    | exact resolve eq6905 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6972 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq6905
    | (have j0 := eq6905 (σ y) X0 (σ x)
       grind)
    | exact resolve eq6905 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7048 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) X0)) = (M.op y (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq704 X0
       have i₂ := eq6905 X0 X0 sF0
       grind)
    | exact superpose eq6905 eq704
    | exact resolve eq704 eq6905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq7050 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X0)) = (M.op (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq705 X0
       have i₂ := eq6905 X0 X0 sF4
       grind)
    | exact superpose eq6905 eq705
    | exact resolve eq705 eq6905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq7776 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq87 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq87
    | (have j0 := eq87 x
       grind)
    | exact resolve eq87 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq7804 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7776
  have eq7814 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq7804
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq7804
    | exact resolve eq7804 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7804
  have eq7831 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq7814
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq7814 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7814
  have eq7835 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq7831 eq49
    | exact resolve eq49 eq7831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq7968 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq88 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq88
    | (have j0 := eq88 y
       grind)
    | exact resolve eq88 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq7995 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq7968
  have eq8004 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7995
       have i₂ := eq79
       grind)
    | exact superpose eq79 eq7995
    | exact resolve eq7995 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq7995
  have eq8028 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq8004
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq8004 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8004
  have eq8054 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq8028 eq111
    | exact resolve eq111 eq8028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq8431 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq133
    | (have j0 := eq133 (M.op x y)
       grind)
    | exact resolve eq133 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq8454 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq8431
  have eq8461 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq132 eq8454
    | exact resolve eq8454 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq8454
  have eq8492 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq8461
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq8461 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461
  have eq10198 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y (M.op X1 y)) X0)) = (M.op (M.op x y) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 X1
       have i₂ := eq6905 X0 X0 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq6905 eq424
    | exact resolve eq424 eq6905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq10227 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq10198 X0 x
       grind)
    | exact superpose eq10198 eq52
    | exact resolve eq52 eq10198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10198
  have eq10368 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq10227 (M.op X0 (M.op X0 X0))
       have i₂ := eq252 X0 X0 X0
       grind)
    | exact superpose eq252 eq10227
    | exact resolve eq10227 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10492 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1169 X0
       have i₂ := eq10368 X0
       grind)
    | exact superpose eq10368 eq1169
    | exact resolve eq1169 eq10368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq10513 : (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq7050 sF4
       have i₂ := eq10368 sF4
       grind)
    | exact superpose eq10368 eq7050
    | exact resolve eq7050 eq10368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7050
  have eq10584 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) (M.op (M.op (M.op x y) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq10368 eq14
    | exact resolve eq14 eq10368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10610 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10584 X0 X1
       have i₂ := eq14 X0 sF0 X0
       grind)
    | exact superpose eq14 eq10584
    | exact resolve eq10584 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10584
  have eq10645 : (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3876 eq10513
    | exact resolve eq10513 eq3876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10513
  have eq10721 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X1
       have i₂ := eq6905 X0 X0 (M.op sF3 (M.op X1 sF3))
       grind)
    | exact superpose eq6905 eq425
    | exact resolve eq425 eq6905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq11015 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq10721 eq52
    | exact resolve eq52 eq10721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10721
  have eq11172 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq11015 (M.op X0 (M.op X0 X0))
       have i₂ := eq252 X0 X0 X0
       grind)
    | exact superpose eq252 eq11015
    | exact resolve eq11015 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq11015
  have eq11479 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op (M.op x y) (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq715 X0 X1 X2
       have i₂ := eq10610 (M.op y sF0) (M.op y sF0)
       grind)
    | exact superpose eq10610 eq715
    | exact resolve eq715 eq10610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq11480 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x y)) y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3723 eq11479
    | exact resolve eq11479 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723 eq11479
  have eq11481 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X1 (M.op X2 (M.op X0 x))) (M.op y (M.op y (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq6960 eq11480
    | exact resolve eq11480 eq6960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6960 eq11480
  have eq11632 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq11172 eq14
    | exact resolve eq14 eq11172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11172
  have eq11658 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11632 X0 X1
       have i₂ := eq14 X0 sF4 X0
       grind)
    | exact superpose eq14 eq11632
    | exact resolve eq11632 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11632
  have eq11788 : (M.op y y) = (M.op x (M.op y (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq11481 (M.op x (M.op x x)) x x
       have i₂ := eq52 x x x
       grind)
    | exact superpose eq52 eq11481
    | exact resolve eq11481 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11481
  have eq12335 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq11658 eq716
    | exact resolve eq716 eq11658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq11658
  have eq12336 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3901 eq12335
    | exact resolve eq12335 eq3901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3901 eq12335
  have eq12337 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X1 (M.op X2 (M.op X0 (σ x)))) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq6972 eq12336
    | exact resolve eq12336 eq6972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6972 eq12336
  have eq12408 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq12337 (M.op x (M.op x x)) x sF2
       have i₂ := eq52 x x sF2
       grind)
    | exact superpose eq52 eq12337
    | exact resolve eq12337 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12337
  have eq13791 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X2)) X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq422 X0 X1 X2 X3
       have i₂ := eq6905 X0 X0 (M.op X2 (M.op X3 X2))
       grind)
    | exact superpose eq6905 eq422
    | exact resolve eq422 eq6905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq14048 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 x X2
       have i₂ := eq13791 X2 X0 X1 x
       grind)
    | exact superpose eq13791 eq52
    | exact resolve eq52 eq13791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13791
  have eq14644 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op (M.op X1 X0) (M.op y (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq3678 eq14048
    | exact resolve eq14048 eq3678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14048
  have eq15729 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10645 eq12408
    | exact resolve eq12408 eq10645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10645 eq12408
  have eq30821 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq7831 eq100
    | exact resolve eq100 eq7831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq30832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq105 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30840 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq30832
    | exact resolve eq30832 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30832
  have eq30851 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq30840
       have r₂ := eq27
       grind)
    | exact resolve eq30840 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30840
  have eq30853 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq30851
    | exact resolve eq30851 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30851
  have eq30857 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30853 eq51
    | exact resolve eq51 eq30853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30863 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30853 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq30853
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq30853
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq30853
       grind)
    | exact resolve eq12 eq30853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30864 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30853 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq30853
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq30853
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq30853
       grind)
    | exact resolve eq13 eq30853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30853
  have eq30898 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq30864
  have eq30899 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq30863
  have eq30927 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq30899
    | exact resolve eq30899 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30899
  have eq30928 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq30927
  have eq30933 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq30857
    | exact resolve eq30857 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30857
  have eq30947 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq3876 eq30933
    | exact resolve eq30933 eq3876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3876 eq30933
  have eq31859 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30898 eq105
    | exact resolve eq105 eq30898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30898
  have eq31873 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31859
  have eq31962 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1)))) X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq417 X0 X1 X2 X3
       have i₂ := eq6905 X0 X0 (M.op (M.op X1 (M.op X2 X1)) (M.op X3 (M.op X1 (M.op X2 X1))))
       grind)
    | exact superpose eq6905 eq417
    | exact resolve eq417 eq6905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417 eq6905
  have eq32001 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq31873
       grind)
    | exact superpose eq31873 eq50
    | exact resolve eq50 eq31873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31873
  have eq32073 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32001
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32001
    | exact resolve eq32001 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32001
  have eq32085 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3678 eq32073
    | exact resolve eq32073 eq3678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32073
  have eq32386 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 (M.op X2 X0)) x X1
       have i₂ := eq31962 X1 X0 X2 x
       grind)
    | exact superpose eq31962 eq52
    | exact resolve eq52 eq31962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq31962
  have eq33103 : ∀ X0 : G, y = (M.op (M.op X0 x) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32085 eq53
    | exact resolve eq53 eq32085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33202 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33103 x
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq33103
    | exact resolve eq33103 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33103
  have eq36060 : x ≠ y ∨ y = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq33202
       grind)
    | exact superpose eq33202 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq33202
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq33202
       grind)
    | exact resolve eq13 eq33202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40287 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30928 eq60
    | exact resolve eq60 eq30928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq30928
  have eq40309 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq40287
    | exact resolve eq40287 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40287
  have eq40312 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq30947 eq54
    | exact resolve eq54 eq30947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq30947
  have eq40420 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40312 x
       have i₂ := eq56 sF2 x
       grind)
    | exact superpose eq56 eq40312
    | exact resolve eq40312 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40312
  have eq41490 : y ≠ y ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq40309
       grind)
    | exact superpose eq40309 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq40309
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq40309
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq40309
       grind)
    | exact resolve eq12 eq40309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40309
  have eq41535 : y ≠ y ∨ x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq41490
  have eq41536 : x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq41535
  have eq41568 : x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41536
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41536
    | exact resolve eq41536 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41536
  have eq41569 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41568
  have eq41599 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq41569
       grind)
    | exact superpose eq41569 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq41569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41569
  have eq41614 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41599
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41599
    | exact resolve eq41599 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41599
  have eq41615 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41614
  have eq44101 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8028 eq112
    | exact resolve eq112 eq8028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq8028
  have eq44371 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq40420 eq7835
    | exact resolve eq7835 eq40420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40420
  have eq44506 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq44371
    | exact resolve eq44371 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44371
  have eq46279 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3678 eq156
    | exact resolve eq156 eq3678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq46280 : (σ (M.op y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8492 eq46279
    | exact resolve eq46279 eq8492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46279
  have eq46281 : (σ (M.op y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq3678 eq46280
    | exact resolve eq46280 eq3678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46280
  have eq47364 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq41615
       grind)
    | exact superpose eq41615 eq50
    | exact resolve eq50 eq41615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47414 : x ≠ y ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41615
  have eq47458 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47364
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq47364
    | exact resolve eq47364 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47364
  have eq47475 : x = (M.op y (M.op x y)) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3678 eq47458
    | exact resolve eq47458 eq3678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3678 eq47458
  have eq69626 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30821
       have i₂ := eq33202
       grind)
    | exact superpose eq33202 eq30821
    | exact resolve eq30821 eq33202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30821 eq33202
  have eq69695 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq69626
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq69626
    | exact resolve eq69626 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69626
  have eq72109 : (τ (σ y)) = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69695 eq7835
    | exact resolve eq7835 eq69695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7835 eq69695
  have eq72268 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq72109
    | exact resolve eq72109 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72109
  have eq72283 : y = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq72268
       have r₂ := eq36060
       grind)
    | exact resolve eq72268 eq36060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36060 eq72268
  have eq72288 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq72283
       grind)
    | exact superpose eq72283 eq43
    | exact resolve eq43 eq72283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq72283
  have eq72336 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7831 eq72288
    | exact resolve eq72288 eq7831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7831 eq72288
  have eq72353 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq72336
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq72336
    | exact resolve eq72336 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72336
  have eq72405 : (M.op (σ x) (σ y)) = (M.op y (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72353 eq10368
    | exact resolve eq10368 eq72353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10368 eq72353
  have eq72515 : (M.op (σ x) (σ y)) = (M.op y (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq72405
    | exact resolve eq72405 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72405
  have eq78439 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq47475 eq46281
    | exact resolve eq46281 eq47475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47475
  have eq78443 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32085 eq46281
    | exact resolve eq46281 eq32085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32085 eq46281
  have eq78505 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq78443
  have eq78507 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq78439
  have eq78517 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78505
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78505
    | exact resolve eq78505 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78505
  have eq78519 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78507
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78507
    | exact resolve eq78507 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78507
  have eq78547 : (σ (M.op x y)) = (M.op y (M.op (M.op x y) (σ x))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78517 eq10227
    | exact resolve eq10227 eq78517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10227 eq78517
  have eq170557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78547 eq72515
    | exact resolve eq72515 eq78547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72515 eq78547
  have eq170663 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq170557
  have eq170711 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq170663
       have r₂ := eq27
       grind)
    | exact resolve eq170663 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170663
  have eq170738 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq170711 eq71
    | (have r₁ := eq71
       have r₂ := eq170711
       grind)
    | exact resolve eq71 eq170711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq170739 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq170711 eq223
    | exact resolve eq223 eq170711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq170802 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq170711 eq15729
    | exact resolve eq15729 eq170711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171156 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq170738
  have eq171195 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10492 eq170802
    | exact resolve eq170802 eq10492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170802
  have eq171215 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq170739
    | exact resolve eq170739 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170739
  have eq171332 : (τ (σ x)) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq171195 eq8054
    | exact resolve eq8054 eq171195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171382 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq171195 eq51
    | exact resolve eq51 eq171195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq171195
  have eq171624 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq171332
    | exact resolve eq171332 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171332
  have eq171648 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq171215 eq8054
    | exact resolve eq8054 eq171215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171215
  have eq172096 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq171624
       grind)
    | exact superpose eq171624 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq171624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172116 : y = (M.op y y) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq172096
  have eq172349 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq171624
       have i₂ := eq171648
       grind)
    | exact superpose eq171648 eq171624
    | exact resolve eq171624 eq171648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171624 eq171648
  have eq172373 : x = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq172349
  have eq173610 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq170711 eq171382
    | exact resolve eq171382 eq170711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170711 eq171382
  have eq173756 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq173610
  have eq315680 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78519 eq56
    | exact resolve eq56 eq78519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78519
  have eq326040 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq171156 eq105
    | exact resolve eq105 eq171156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq171156
  have eq326066 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq326040
  have eq328314 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq326066 eq173756
    | exact resolve eq173756 eq326066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173756 eq326066
  have eq328480 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq328314
  have eq328625 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq328480
    | exact resolve eq328480 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328480
  have eq328973 : (M.op x y) = (M.op x (M.op y (M.op y (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14644 x y
       have i₂ := eq328625
       grind)
    | exact superpose eq328625 eq14644
    | exact resolve eq14644 eq328625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14644 eq328625
  have eq329058 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11788 eq328973
    | exact resolve eq328973 eq11788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11788 eq328973
  have eq337578 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq172116
       have i₂ := eq329058
       grind)
    | exact superpose eq329058 eq172116
    | exact resolve eq172116 eq329058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329058
  have eq337762 : x ≠ y ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq172116
  have eq337786 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq337578
  have eq338224 : x = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq337786 eq172373
    | exact resolve eq172373 eq337786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172373 eq337786
  have eq338559 : x = (τ (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq338224
  have eq338887 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq338559
    | exact resolve eq338559 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338559
  have eq342019 : y = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq338887 eq29
    | exact resolve eq29 eq338887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338887
  have eq342787 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq342019
    | exact resolve eq342019 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342019
  have eq342788 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq342787
  have eq342812 : (σ y) = (σ (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq342788 eq20
    | exact resolve eq20 eq342788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342788
  have eq343393 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq342812
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq342812
    | exact resolve eq342812 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342812
  have eq343451 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq343393 eq26
    | exact resolve eq26 eq343393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344266 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq343451 eq315680
    | exact resolve eq315680 eq343451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315680 eq343451
  have eq344350 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq344266
  have eq344382 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq344350
       have r₂ := eq47414
       grind)
    | exact resolve eq344350 eq47414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47414 eq344350
  have eq344424 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq344382
       grind)
    | exact superpose eq344382 eq50
    | exact resolve eq50 eq344382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq358748 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq337762
       have r₂ := eq343393
       grind)
    | exact resolve eq337762 eq343393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337762 eq343393
  have eq358893 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq358748
       grind)
    | exact superpose eq358748 eq56
    | exact resolve eq56 eq358748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358748
  have eq359005 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq358893
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq358893
    | exact resolve eq358893 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358893
  have eq359006 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq359005
  have eq359050 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq359006 eq29
    | exact resolve eq29 eq359006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq359006
  have eq359843 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq359050
    | exact resolve eq359050 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq359050
  have eq359868 : ∀ X0 : G, (M.op y (M.op X0 (M.op y X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq359843 eq50
    | exact resolve eq50 eq359843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq359869 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq359843 eq53
    | exact resolve eq53 eq359843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq360207 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq359843
  have eq391235 : x = (M.op y (M.op x x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq359868 x
       have i₂ := eq344382
       grind)
    | exact superpose eq344382 eq359868
    | exact resolve eq359868 eq344382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359868
  have eq391482 : x = (M.op y (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq391235
  have eq391636 : x = (M.op x (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq391482
       have i₂ := eq7048 x
       grind)
    | exact superpose eq7048 eq391482
    | exact resolve eq391482 eq7048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7048 eq391482
  have eq393131 : ∀ X1 : G, (M.op (M.op (M.op y y) y) (M.op (M.op y y) (M.op X1 X1))) = X1 ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq32386 (M.op y y) X1 (M.op x x)
       have i₂ := eq359869 x
       grind)
    | exact superpose eq359869 eq32386
    | exact resolve eq32386 eq359869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32386 eq359869
  have eq393205 : ∀ X1 : G, (M.op (M.op x y) (M.op (M.op y y) (M.op X1 X1))) = X1 ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq393131 X1
       have i₂ := eq10610 (M.op (M.op y y) (M.op X1 X1)) (M.op y y)
       grind)
    | exact superpose eq10610 eq393131
    | exact resolve eq393131 eq10610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393131
  have eq393276 : ∀ X1 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op X1 X1))) = X1 ∨ x = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq393205 X1
       have i₂ := eq10610 (M.op X1 X1) y
       grind)
    | exact superpose eq10610 eq393205
    | exact resolve eq393205 eq10610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10610 eq393205
  have eq417570 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq344424 eq393276
    | exact resolve eq393276 eq344424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344424 eq393276
  have eq417733 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq417570
  have eq520593 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq417733 eq391636
    | exact resolve eq391636 eq417733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391636 eq417733
  have eq520762 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq520593
  have eq520966 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3804 x
       have i₂ := eq520762
       grind)
    | exact superpose eq520762 eq3804
    | exact resolve eq3804 eq520762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520762
  have eq521276 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44506
       have i₂ := eq520966
       grind)
    | exact superpose eq520966 eq44506
    | exact resolve eq44506 eq520966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44506 eq520966
  have eq521327 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq521276
  have eq521353 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq521327
       have r₂ := eq360207
       grind)
    | exact resolve eq521327 eq360207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521327
  have eq521904 : x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq344382
       have i₂ := eq521353
       grind)
    | exact superpose eq521353 eq344382
    | exact resolve eq344382 eq521353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344382 eq521353
  have eq522035 : x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq521904
  have eq522124 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq522035
       have r₂ := eq360207
       grind)
    | exact resolve eq522035 eq360207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522035
  have eq522246 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op y (M.op (M.op x y) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq522124 eq15729
    | exact resolve eq15729 eq522124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15729 eq522124
  have eq523100 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10492 eq522246
    | exact resolve eq522246 eq10492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10492 eq522246
  have eq523329 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq523100 eq8054
    | exact resolve eq8054 eq523100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8054 eq523100
  have eq523827 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq523329
    | exact resolve eq523329 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq523329
  have eq525573 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq523827
       grind)
    | exact superpose eq523827 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq523827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525595 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq525573
  have eq3408112 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3804 y
       have i₂ := eq525595
       grind)
    | exact superpose eq525595 eq3804
    | exact resolve eq3804 eq525595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3804 eq525595
  have eq3609500 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq523827
       have i₂ := eq3408112
       grind)
    | exact superpose eq3408112 eq523827
    | exact resolve eq523827 eq3408112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523827 eq3408112
  have eq3609708 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq3609500
  have eq3609856 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3609708
       have r₂ := eq360207
       grind)
    | exact resolve eq3609708 eq360207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360207 eq3609708
  have eq3610572 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq3609856
       grind)
    | exact superpose eq3609856 eq56
    | exact resolve eq56 eq3609856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3609856
  have eq3611001 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3610572
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3610572
    | exact resolve eq3610572 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3610572
  have eq3611002 : x = (M.op x y) := by grind
  clear eq3611001
  have eq3611279 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq3611002 eq20
    | exact resolve eq20 eq3611002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq3611284 : x ≠ x ∨ x = (k x y) := by
    first
    | exact superpose eq3611002 eq66
    | (have r₁ := eq66
       have r₂ := eq3611002
       grind)
    | exact resolve eq66 eq3611002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq3611330 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq3611002 eq214
    | exact resolve eq214 eq3611002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq3611863 : x = (k x y) := by grind
  clear eq3611284
  have eq3612028 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3611330
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3611330
    | exact resolve eq3611330 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3611330
  have eq3612073 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq3611279
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3611279
    | exact resolve eq3611279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3611279
  have eq3612094 : x = (M.op y y) := by
    first
    | exact superpose eq3611002 eq3612028
    | exact resolve eq3612028 eq3611002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3611002 eq3612028
  have eq3612155 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3612073 eq26
    | exact resolve eq26 eq3612073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3616709 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq3611863
       grind)
    | exact superpose eq3611863 eq44
    | exact resolve eq44 eq3611863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3611863
  have eq3616978 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3612073 eq3616709
    | exact resolve eq3616709 eq3612073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616709
  have eq3617082 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq3616978
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3616978
    | exact resolve eq3616978 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3616978
  have eq3617182 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq3612073 eq3617082
    | exact resolve eq3617082 eq3612073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3617082
  have eq3617702 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq44101
       have i₂ := eq3612094
       grind)
    | exact superpose eq3612094 eq44101
    | exact resolve eq44101 eq3612094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44101 eq3612094
  have eq3618772 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3617702
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3617702
    | exact resolve eq3617702 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3617702
  have eq3618998 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3612073 eq3618772
    | exact resolve eq3618772 eq3612073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3618772
  have eq3693292 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3618998 eq56
    | exact resolve eq56 eq3618998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq3618998
  have eq3693728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3612155 eq3693292
    | exact resolve eq3693292 eq3612155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693292
  have eq3694063 : x = y := by
    first
    | (have r₁ := eq3693728
       have r₂ := eq27
       grind)
    | exact resolve eq3693728 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693728
  have eq3694466 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3694063
       grind)
    | exact superpose eq3694063 eq24
    | exact resolve eq24 eq3694063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3694489 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq131
       have i₂ := eq3694063
       grind)
    | exact superpose eq3694063 eq131
    | exact resolve eq131 eq3694063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq3694063
  have eq3696379 : (σ (M.op x y)) = (σ (k (M.op x y) x)) := by
    first
    | exact superpose eq3617182 eq3694489
    | exact resolve eq3694489 eq3617182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3617182 eq3694489
  have eq3696401 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3694466
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3694466
    | exact resolve eq3694466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3694466
  have eq3696691 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq130 eq3696379
    | exact resolve eq3696379 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq3696379
  have eq3696712 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3612073 eq3696401
    | exact resolve eq3696401 eq3612073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696401
  have eq3696872 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3612073 eq3696691
    | exact resolve eq3696691 eq3612073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3612073 eq3696691
  have eq3696974 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8492 eq3696872
    | exact resolve eq3696872 eq8492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8492 eq3696872
  have eq3698724 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3696712 eq3612155
    | exact resolve eq3612155 eq3696712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3612155 eq3696712
  have eq3728354 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3696974 eq3698724
    | exact resolve eq3698724 eq3696974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696974 eq3698724
  have eq3728355 : False := by grind
  exact eq3728355

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq25 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X0
       have i₂ := eq9 X0 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq57
    | (have j0 := eq57 (σ X0) (σ X1)
       grind)
    | exact resolve eq57 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq84 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq83
    | exact resolve eq83 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq84
    | exact resolve eq84 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq84
  have eq96 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq92 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq92
    | exact resolve eq92 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq140 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq68 y x
       grind)
    | exact superpose eq68 eq16
    | (have j1 := eq68 y x
       grind)
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq163 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq25 (σ X0) (σ X0)
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq25
    | exact resolve eq25 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140
       have i₂ := eq57 y x
       grind)
    | exact superpose eq57 eq140
    | (have j1 := eq57 (σ y) (σ x)
       grind)
    | exact resolve eq140 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq140
  have eq617 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq616
  have eq625 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq25 y x
       have i₂ := eq617
       grind)
    | exact superpose eq617 eq25
    | exact resolve eq25 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98004 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq625
       grind)
    | exact superpose eq625 eq16
    | exact resolve eq16 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq98239 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq98004
       have i₂ := eq617
       grind)
    | exact superpose eq617 eq98004
    | exact resolve eq98004 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq98004
  have eq98240 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq98239
  have eq98266 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25 (σ y) (σ x)
       have i₂ := eq98240
       grind)
    | exact superpose eq98240 eq25
    | exact resolve eq25 eq98240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98400 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq98266
       have i₂ := eq96 y
       grind)
    | exact superpose eq96 eq98266
    | exact resolve eq98266 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq98266
  have eq587415 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq98240
       have i₂ := eq98400
       grind)
    | exact superpose eq98400 eq98240
    | exact resolve eq98240 eq98400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98240 eq98400
  have eq587717 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq587415
  have eq588148 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq587717
       grind)
    | exact superpose eq587717 eq10
    | exact resolve eq10 eq587717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587717
  have eq588601 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq588148
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq588148
    | exact resolve eq588148 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588148
  have eq588602 : x = (M.op y y) := by grind
  clear eq588601
  have eq589746 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq163 y
       have i₂ := eq588602
       grind)
    | exact superpose eq588602 eq163
    | exact resolve eq163 eq588602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq590030 : x = (M.op x y) := by
    first
    | (have i₁ := eq25 y y
       have i₂ := eq588602
       grind)
    | exact superpose eq588602 eq25
    | exact resolve eq25 eq588602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq588602
  have eq673636 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq589746
       grind)
    | exact superpose eq589746 eq16
    | exact resolve eq16 eq589746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589746
  have eq674063 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq673636
       have i₂ := eq590030
       grind)
    | exact superpose eq590030 eq673636
    | exact resolve eq673636 eq590030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590030 eq673636
  have eq674064 : False := by grind
  exact eq674064

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_y_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq42 : ∀ X0 X1 : G, (σ (k X1 (k x X0))) = (k (σ X1) (k (σ x) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X0
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : x ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq184 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq174 (M.op y y)
       have i₂ := eq16 y y y
       grind)
    | exact superpose eq16 eq174
    | exact resolve eq174 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : y = (M.op (M.op x y) (M.op y (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq184
       grind)
    | exact superpose eq184 eq174
    | exact resolve eq174 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : y ≠ (M.op (M.op x y) y) ∨ (k y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq184
       grind)
    | exact superpose eq184 eq13
    | exact resolve eq13 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 y
       have i₂ := eq184
       grind)
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq175 (M.op sF3 sF3)
       have i₂ := eq16 sF3 sF3 sF3
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq206 : (M.op (M.op y (M.op x y)) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq177 eq180
    | exact resolve eq180 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k x y) := by
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
  have eq640 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
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
  have eq641 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq184
       grind)
    | exact superpose eq184 eq11
    | exact resolve eq11 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq641
  have eq736 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq653 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq653 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq653 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq653 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq737 : (k y y) = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq709
       have r₂ := eq189
       grind)
    | exact resolve eq709 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq709
  have eq740 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (k y y))) := by
    intro X0
    first
    | exact superpose eq737 eq190
    | exact resolve eq190 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq741 : y = (M.op (M.op x y) (M.op y (k y y))) := by
    first
    | exact superpose eq737 eq188
    | exact resolve eq188 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq745 : (M.op y y) = (M.op (k y y) y) := by
    first
    | exact superpose eq737 eq180
    | exact resolve eq180 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq749 : (M.op (M.op x y) y) = (M.op (k y y) y) := by
    first
    | (have i₁ := eq745
       have i₂ := eq184
       grind)
    | exact superpose eq184 eq745
    | exact resolve eq745 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq751 : (k y y) = (M.op (k y y) y) := by
    first
    | exact superpose eq737 eq749
    | exact resolve eq749 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq765 : (k y y) ≠ (k y y) ∨ (M.op y (k y y)) = (k y (k y y)) := by
    first
    | (have i₁ := eq13 y (k y y)
       have i₂ := eq751
       grind)
    | exact superpose eq751 eq13
    | (have j0 := eq13 y (k y y)
       grind)
    | (have r₁ := eq13 y (k y y)
       have r₂ := eq751
       grind)
    | exact resolve eq13 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : (M.op y (k y y)) = (k y (k y y)) := by grind
  clear eq765
  have eq881 : ∀ X0 : G, y = (M.op (M.op X0 y) (k y (k y y))) := by
    intro X0
    first
    | (have i₁ := eq740 X0
       have i₂ := eq768
       grind)
    | exact superpose eq768 eq740
    | exact resolve eq740 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq882 : y = (M.op (M.op x y) (k y (k y y))) := by
    first
    | (have i₁ := eq741
       have i₂ := eq768
       grind)
    | exact superpose eq768 eq741
    | exact resolve eq741 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq1007 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq640
       grind)
    | exact superpose eq640 eq39
    | exact resolve eq39 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1008 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1007
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1007
    | exact resolve eq1007 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1010 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1008
    | exact resolve eq1008 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1010 eq646
    | exact resolve eq646 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1169 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1162
       have r₂ := eq27
       grind)
    | exact resolve eq1162 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1176 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1169 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1169
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1169
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1169
       grind)
    | exact resolve eq12 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1184 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1176
  have eq1189 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1184
    | exact resolve eq1184 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184
  have eq1190 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1189
  have eq1221 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1190 eq107
    | exact resolve eq107 eq1190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1190
  have eq1228 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1221
    | exact resolve eq1221 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1231 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq640 eq1228
    | exact resolve eq1228 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq1228
  have eq1232 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1231
  have eq1262 : y ≠ y ∨ x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq1232
       grind)
    | exact superpose eq1232 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1232
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1232
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1232
       grind)
    | exact resolve eq12 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1263 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1232
       grind)
    | exact superpose eq1232 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1232
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1232
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1232
       grind)
    | exact resolve eq13 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1269 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1263
  have eq1270 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1262
  have eq1274 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1269
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1269
    | exact resolve eq1269 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1269
  have eq1275 : x = (M.op x y) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1270
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1270
    | exact resolve eq1270 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq1276 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1275
  have eq1301 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1274
       grind)
    | exact superpose eq1274 eq40
    | exact resolve eq40 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274
  have eq1304 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1301
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1301
    | exact resolve eq1301 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1306 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1304
    | exact resolve eq1304 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1310 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq1276
       grind)
    | exact superpose eq1276 eq36
    | exact resolve eq36 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq1319 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1310
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1310
    | exact resolve eq1310 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1371 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1319 eq646
    | exact resolve eq646 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1379 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1371
  have eq1431 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1379 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1379
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1379
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1379
       grind)
    | exact resolve eq13 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379
  have eq1437 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1431
  have eq1442 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1437
    | exact resolve eq1437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1306 eq1442
    | exact resolve eq1442 eq1306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306 eq1442
  have eq1447 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1445
       have r₂ := eq27
       grind)
    | exact resolve eq1445 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq1452 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1447 eq192
    | exact resolve eq192 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq1460 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1452
    | exact resolve eq1452 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq1462 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1447 eq1460
    | exact resolve eq1460 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447 eq1460
  have eq1468 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1462 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1470 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1462 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq1462
       grind)
    | exact resolve eq13 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1476 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1468
  have eq1481 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1476
       have r₂ := eq1470
       grind)
    | exact resolve eq1476 eq1470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470 eq1476
  have eq1490 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1481 eq115
    | exact resolve eq115 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1481
  have eq1501 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1490
    | exact resolve eq1490 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1490
  have eq1510 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq751
       have i₂ := eq1501
       grind)
    | exact superpose eq1501 eq751
    | exact resolve eq751 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq1511 : (k y x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq768
       have i₂ := eq1501
       grind)
    | exact superpose eq1501 eq768
    | exact resolve eq768 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq1501
  have eq1527 : (k y x) = (M.op y x) := by
    first
    | (have r₁ := eq1511
       have r₂ := eq181
       grind)
    | exact resolve eq1511 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1528 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1510
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1510
    | exact resolve eq1510 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1529 : x = (M.op x y) := by grind
  clear eq1528
  have eq1535 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq18
    | exact resolve eq18 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1536 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq22
    | exact resolve eq22 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1537 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq35
    | exact resolve eq35 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1538 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq39
    | exact resolve eq39 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1540 : (M.op x y) ≠ (M.op x y) ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq181
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq181
    | (have r₁ := eq181
       have r₂ := eq1529
       grind)
    | exact resolve eq181 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq1541 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ y = (k (M.op x y) y) := by
    first
    | (have i₁ := eq623
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq623
    | (have r₁ := eq623
       have r₂ := eq1529
       grind)
    | exact resolve eq623 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq1542 : y = (k (M.op x y) y) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq1541
  have eq1543 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
  clear eq1540
  have eq1546 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1536 eq20
    | exact resolve eq20 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1606 : (M.op x y) = (k y y) := by
    first
    | exact superpose eq1535 eq737
    | exact resolve eq737 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1686 : y = (M.op (k y x) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq177 y
       have i₂ := eq1527
       grind)
    | exact superpose eq1527 eq177
    | exact resolve eq177 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1689 : y ≠ (k y x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1527
       grind)
    | exact superpose eq1527 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527
  have eq1700 : y ≠ (k y (M.op x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1689
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq1689
    | exact resolve eq1689 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1703 : y = (M.op (k y x) (k y (M.op x y))) := by
    first
    | exact superpose eq1543 eq1686
    | exact resolve eq1686 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq1709 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ y ≠ (k y (M.op x y)) := by
    first
    | (have i₁ := eq1700
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq1700
    | exact resolve eq1700 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq1712 : y = (M.op (k y (M.op x y)) (k y (M.op x y))) := by
    first
    | (have i₁ := eq1703
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq1703
    | exact resolve eq1703 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq1717 : (k y y) = (k (M.op x y) y) ∨ y ≠ (k y (M.op x y)) := by
    first
    | exact superpose eq737 eq1709
    | exact resolve eq1709 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709
  have eq1719 : y ≠ (k y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq1717
       have i₂ := eq1606
       grind)
    | exact superpose eq1606 eq1717
    | exact resolve eq1717 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1748 : (M.op y (k y (M.op x y))) = (M.op (k y (M.op x y)) (k y (M.op x y))) := by
    first
    | exact superpose eq1543 eq206
    | exact resolve eq206 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq1771 : y = (M.op y (k y (M.op x y))) := by
    first
    | exact superpose eq1712 eq1748
    | exact resolve eq1748 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq1883 : ∀ X0 X1 : G, (M.op (k y (k y y)) y) = (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op (M.op (k y (k y y)) y) (k y (k y y)))) := by
    intro X0 X1
    first
    | exact superpose eq882 eq179
    | exact resolve eq179 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq882
  have eq1927 : ∀ X0 X1 : G, (M.op (k y (k y y)) y) = (M.op (M.op X0 (M.op X1 (M.op x y))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq1883 X0 X1
       have i₂ := eq881 (k y (k y y))
       grind)
    | exact superpose eq881 eq1883
    | exact resolve eq1883 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq1883
  have eq1966 : ∀ X0 X1 : G, (M.op (k y (M.op x y)) y) = (M.op (M.op X0 (M.op X1 (M.op x y))) y) := by
    intro X0 X1
    first
    | (have i₁ := eq1927 X0 X1
       have i₂ := eq1606
       grind)
    | exact superpose eq1606 eq1927
    | exact resolve eq1927 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq2159 : (k y (M.op x y)) = (M.op (M.op x y) (M.op (k y (M.op x y)) y)) := by
    first
    | exact superpose eq1771 eq174
    | exact resolve eq174 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq2162 : y ≠ y ∨ (M.op (k y (M.op x y)) y) = (k (k y (M.op x y)) y) := by
    first
    | exact superpose eq1771 eq13
    | (have j0 := eq13 (k y (M.op x y)) y
       grind)
    | (have r₁ := eq13 (k y (M.op x y)) y
       have r₂ := eq1771
       grind)
    | exact resolve eq13 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771
  have eq2171 : (M.op (k y (M.op x y)) y) = (k (k y (M.op x y)) y) := by grind
  clear eq2162
  have eq2177 : (k y (M.op x y)) = (M.op (M.op x y) (k (k y (M.op x y)) y)) := by
    first
    | exact superpose eq2171 eq2159
    | exact resolve eq2159 eq2171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2159
  have eq2514 : y = (k (k y (M.op x y)) (k y (M.op x y))) ∨ y = (k y (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq1712 eq11
    | exact resolve eq11 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2516 : y ≠ (k y (M.op x y)) ∨ y = (k (k y (M.op x y)) (k y (M.op x y))) := by
    first
    | exact superpose eq1712 eq13
    | exact resolve eq13 eq1712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712
  have eq2526 : y = (k (k y (M.op x y)) (k y (M.op x y))) ∨ y = (k y (M.op x y)) := by grind
  clear eq2514
  have eq2531 : y = (k (k y (M.op x y)) (k y (M.op x y))) := by
    first
    | (have r₁ := eq2526
       have r₂ := eq2516
       grind)
    | exact resolve eq2526 eq2516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2516 eq2526
  have eq2813 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1542 eq1537
    | exact resolve eq1537 eq1542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq1542
  have eq2827 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2813
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2813
    | exact resolve eq2813 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2813
  have eq2830 : (σ y) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq1543 eq2827
    | exact resolve eq2827 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543 eq2827
  have eq2844 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq2830 eq736
    | (have j0 := eq736 (σ x) (σ y)
       grind)
    | (have r₁ := eq736 (σ x) (σ y)
       have r₂ := eq2830
       grind)
    | exact resolve eq736 eq2830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq2845 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq2830 eq702
    | (have j0 := eq702 (σ y) (σ x)
       grind)
    | (have r₁ := eq702 (σ y) (σ x)
       have r₂ := eq2830
       grind)
    | exact resolve eq702 eq2830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq2830
  have eq2846 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by grind
  clear eq2845
  have eq2847 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq2844
  have eq2848 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq2846
    | exact resolve eq2846 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846
  have eq2849 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq2847
    | exact resolve eq2847 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847
  have eq2856 : y = (k y (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2849
    | exact resolve eq2849 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2849
  have eq3495 : y ≠ y ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2856 eq1719
    | (have r₁ := eq1719
       have r₂ := eq2856
       grind)
    | exact resolve eq1719 eq2856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719
  have eq3505 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2856 eq1538
    | exact resolve eq1538 eq2856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538 eq2856
  have eq3512 : (M.op x y) = (k (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3495
  have eq3515 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3505
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3505
    | exact resolve eq3505 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505
  have eq3685 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3512 eq40
    | exact resolve eq40 eq3512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3512
  have eq3691 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3685
    | exact resolve eq3685 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685
  have eq3694 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1546 eq3691
    | exact resolve eq3691 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3691
  have eq3705 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3515 eq646
    | exact resolve eq646 eq3515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq3515
  have eq3720 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3705
  have eq3850 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3720 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3720
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3720
       grind)
    | exact resolve eq13 eq3720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq3863 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3850
  have eq3872 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3863
    | exact resolve eq3863 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863
  have eq3878 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3694 eq3872
    | exact resolve eq3872 eq3694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3694 eq3872
  have eq3879 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3878
  have eq3892 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3879
  have eq4836 : ∀ X0 : G, (σ (k X0 (k x (M.op x y)))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq1536 eq42
    | exact resolve eq42 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq4848 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq4836 X0
       have i₂ := eq1529
       grind)
    | exact superpose eq1529 eq4836
    | exact resolve eq4836 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529 eq4836
  have eq5211 : (M.op y y) = (M.op (k y (M.op x y)) y) := by
    first
    | exact superpose eq177 eq1966
    | exact resolve eq1966 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1966
  have eq5253 : (M.op (M.op x y) y) = (M.op (k y (M.op x y)) y) := by
    first
    | (have i₁ := eq5211
       have i₂ := eq184
       grind)
    | exact superpose eq184 eq5211
    | exact resolve eq5211 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq5211
  have eq5266 : (k y y) = (M.op (k y (M.op x y)) y) := by
    first
    | exact superpose eq737 eq5253
    | exact resolve eq5253 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq5253
  have eq5271 : (M.op x y) = (M.op (k y (M.op x y)) y) := by
    first
    | (have i₁ := eq5266
       have i₂ := eq1606
       grind)
    | exact superpose eq1606 eq5266
    | exact resolve eq5266 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5266
  have eq5280 : (M.op x y) = (k (k y (M.op x y)) y) := by
    first
    | exact superpose eq5271 eq2171
    | exact resolve eq2171 eq5271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171 eq5271
  have eq5320 : (k y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5280 eq2177
    | exact resolve eq2177 eq5280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2177 eq5280
  have eq5349 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | exact superpose eq5320 eq11
    | exact resolve eq11 eq5320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5351 : (M.op x y) ≠ (k y (M.op x y)) ∨ (k y (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5320 eq13
    | exact resolve eq13 eq5320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5320
  have eq5366 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k y (M.op x y)) := by grind
  clear eq5349
  have eq5374 : (k y (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq5366
       have r₂ := eq5351
       grind)
    | exact resolve eq5366 eq5351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5351 eq5366
  have eq5468 : y = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq5374 eq2531
    | exact resolve eq2531 eq5374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531
  have eq5475 : (k (σ y) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq5374 eq36
    | exact resolve eq36 eq5374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq5485 : (k (σ y) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq5475
    | exact resolve eq5475 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5475
  have eq5494 : (k (σ (M.op x y)) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1546 eq5485
    | exact resolve eq5485 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5485
  have eq5498 : (k (σ (M.op x y)) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq5494
    | exact resolve eq5494 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5494
  have eq5501 : (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1546 eq5498
    | exact resolve eq5498 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5498
  have eq7911 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (k (σ x) (σ x))) := by
    first
    | exact superpose eq5468 eq4848
    | exact resolve eq4848 eq5468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4848
  have eq7970 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ x) (σ x))) := by
    first
    | exact superpose eq41 eq7911
    | exact resolve eq7911 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq7911
  have eq7991 : (σ y) = (k (k (σ (M.op x y)) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq1546 eq7970
    | exact resolve eq7970 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7970
  have eq8009 : (σ y) = (k (k (σ (M.op x y)) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq20 eq7991
    | exact resolve eq7991 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7991
  have eq8021 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq1546 eq8009
    | exact resolve eq8009 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009
  have eq8028 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq8021
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8021
    | exact resolve eq8021 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8021
  have eq8754 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq2848 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2848
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2848
       grind)
    | exact resolve eq12 eq2848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848
  have eq8772 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by grind
  clear eq8754
  have eq8791 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq8772
    | exact resolve eq8772 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8772
  have eq8792 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by grind
  clear eq8791
  have eq8806 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq5501 eq8792
    | exact resolve eq8792 eq5501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5501 eq8792
  have eq8817 : (σ x) = (k (σ x) (σ x)) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5374 eq8806
    | exact resolve eq8806 eq5374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5374 eq8806
  have eq9098 : (σ y) = (k (σ x) (σ x)) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8817 eq8028
    | exact resolve eq8028 eq8817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8028
  have eq9121 : (σ x) = (σ y) ∨ y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8817 eq9098
    | exact resolve eq9098 eq8817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8817 eq9098
  have eq9130 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9121
       have r₂ := eq3892
       grind)
    | exact resolve eq9121 eq3892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9121
  have eq9149 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9130 eq5468
    | exact resolve eq5468 eq9130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5468 eq9130
  have eq9195 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9149
       have i₂ := eq1606
       grind)
    | exact superpose eq1606 eq9149
    | exact resolve eq9149 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606 eq9149
  have eq9237 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9195 eq27
    | exact resolve eq27 eq9195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9195
  have eq9252 : y = (M.op x y) := by
    first
    | (have r₁ := eq9237
       have r₂ := eq1546
       grind)
    | exact resolve eq9237 eq1546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9237
  have eq9255 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9252
       grind)
    | exact superpose eq9252 eq24
    | exact resolve eq24 eq9252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9252
  have eq9412 : (σ x) = (σ y) := by
    first
    | exact superpose eq1536 eq9255
    | exact resolve eq9255 eq1536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536 eq9255
  have eq9718 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9412 eq3892
    | (have r₁ := eq3892
       have r₂ := eq9412
       grind)
    | exact resolve eq3892 eq9412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3892 eq9412
  have eq9724 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9718
  have eq9788 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq9724 eq27
    | exact resolve eq27 eq9724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9724
  have eq9808 : False := by grind
  exact eq9808

/-- `Equation1577`: `x = (y ◇ z) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pxy_pyx_pxx_pxy_Equation1577 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1577 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1577.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) (M.op (M.op X1 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 y X0 x
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) (M.op X1 X2) X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ y) X0 (σ x)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq79 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op (M.op X1 (M.op x y)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq79 eq54
    | exact resolve eq54 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq98 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op x X0))) = X0 := by
    intro X0
    first
    | exact superpose eq79 eq9
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq135 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k x y) = (M.op x x) := by
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
  have eq137 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq140 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq140 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq140 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq143 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66 eq137
    | exact resolve eq137 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq154 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq141 (σ X0)
       grind)
    | exact superpose eq141 eq15
    | exact resolve eq15 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq154 X0
       have i₂ := eq141 X0
       grind)
    | exact superpose eq141 eq154
    | exact resolve eq154 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq154
  have eq167 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq92 eq57
    | exact resolve eq57 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq168 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq92 eq9
    | exact resolve eq9 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq202 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq168 eq9
    | exact resolve eq9 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (M.op x (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq202 eq9
    | exact resolve eq9 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq241 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq210 eq9
    | exact resolve eq9 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq363 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq364 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq363
    | exact resolve eq363 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq366 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq364
    | exact resolve eq364 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364
  have eq368 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq366
    | exact resolve eq366 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq375 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq56
    | exact resolve eq56 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq380 : ∀ X0 X1 : G, (M.op (M.op x (M.op y X0)) X1) = (M.op (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) X1
       have i₂ := eq56 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X0) X1
       have i₂ := eq56 (M.op (M.op X1 X0) (M.op X1 X2)) X1 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq155 X0
       grind)
    | exact superpose eq155 eq10
    | exact resolve eq10 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq429 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq429
    | exact resolve eq429 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq552 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op (M.op X1 (M.op X2 X0)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq390 (M.op X1 (M.op X2 X0)) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq390
    | exact resolve eq390 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 X1)
       have i₂ := eq390 X1 X0 (M.op X1 (M.op (M.op X0 X1) X2))
       grind)
    | exact superpose eq390 eq9
    | exact resolve eq9 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq617 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq392 X1 X2 (M.op (M.op X3 X2) (M.op X3 X0))
       have i₂ := eq392 X2 X3 X0
       grind)
    | exact superpose eq392 eq392
    | exact resolve eq392 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op (M.op X2 X3) X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq392 X1 (M.op X2 X3) (M.op X2 (M.op X3 X0))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq392
    | exact resolve eq392 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq626 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) = (M.op X1 (M.op (M.op y X1) X0)) := by
    intro X0 X1
    first
    | exact superpose eq98 eq392
    | exact resolve eq392 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq631 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) = (M.op X1 (M.op (M.op (σ y) X1) X0)) := by
    intro X0 X1
    first
    | exact superpose eq168 eq392
    | exact resolve eq392 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq390 (M.op X1 X0) (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq392 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq392 eq390
    | exact resolve eq390 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq568 X1 (M.op X2 (M.op X0 X2)) X3
       have i₂ := eq390 X2 X0 (M.op (M.op X1 (M.op X2 (M.op X0 X2))) X3)
       grind)
    | exact superpose eq390 eq568
    | exact resolve eq568 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq761 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X3) = (M.op (M.op X2 X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq642 (M.op X1 (M.op (M.op X2 X1) X0)) X2 X3
       have i₂ := eq568 X2 X1 X0
       grind)
    | exact superpose eq568 eq642
    | exact resolve eq642 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op (M.op X1 X2) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq642 (M.op X1 (M.op X2 X0)) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq642
    | exact resolve eq642 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq642 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq642
    | (have j0 := eq642 y x X0
       grind)
    | exact resolve eq642 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 X1 : G, (M.op (M.op x (M.op y X0)) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq52 eq642
    | exact resolve eq642 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq774 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X1) = (M.op (M.op (σ x) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq241 eq642
    | exact resolve eq642 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ y) X0)) X1) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq58 eq642
    | exact resolve eq642 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq787 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 X0 (M.op X0 X1)
       have i₂ := eq642 X1 X0 X0
       grind)
    | exact superpose eq642 eq56
    | exact resolve eq56 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq807 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq568 X1 (M.op X2 (M.op X2 X0)) X3
       have i₂ := eq642 X0 X2 (M.op (M.op X1 (M.op X2 (M.op X2 X0))) X3)
       grind)
    | exact superpose eq642 eq568
    | exact resolve eq568 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 (M.op X1 (M.op X2 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq552 X0 X1 X2 X3
       have i₂ := eq787 (M.op X1 (M.op X2 X0)) X0 X3
       grind)
    | (have i₁ := eq552 X0 X1 X2 X3
       have i₂ := eq787 X0 (M.op X1 (M.op X2 X0)) X3
       grind)
    | exact superpose eq787 eq552
    | exact resolve eq552 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq865 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq622 X0 X1 X2 X3
       have i₂ := eq767 X1 X2 X3 X0
       grind)
    | exact superpose eq767 eq622
    | exact resolve eq622 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq913 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq768 eq568
    | exact resolve eq568 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq768 eq9
    | exact resolve eq9 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) = (σ (M.op y (M.op x (M.op x y)))) := by
    first
    | exact superpose eq768 eq155
    | exact resolve eq155 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq998 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op (M.op x y) y)) := by
    first
    | exact superpose eq97 eq913
    | exact resolve eq913 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq999 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq98 eq913
    | exact resolve eq913 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1013 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op (M.op x y) (M.op y X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq913 eq642
    | exact resolve eq642 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq1014 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x (M.op y (M.op y X0))) X1) := by
    intro X0 X1
    first
    | exact superpose eq772 eq1013
    | exact resolve eq1013 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq1032 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op y X1) X0)) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq999 eq626
    | exact resolve eq626 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq999
  have eq1049 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x y)) (M.op X1 X0)) = (M.op y (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq914 (M.op (M.op X1 sF0) (M.op X1 x))
       have i₂ := eq392 sF0 X1 x
       grind)
    | exact superpose eq392 eq914
    | exact resolve eq914 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1061 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op x (M.op (M.op x y) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq914 eq642
    | exact resolve eq642 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq1070 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq80 eq1049
    | exact resolve eq1049 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1076 : (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) = (σ (M.op x (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq917
       have i₂ := eq1070 sF0
       grind)
    | exact superpose eq1070 eq917
    | exact resolve eq917 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq1070
  have eq1098 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X0 X3))) (M.op (M.op X2 (M.op X0 X1)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X1 X2 (M.op X3 (M.op X0 X3)) X4
       have i₂ := eq390 X3 X0 X1
       grind)
    | exact superpose eq390 eq53
    | exact resolve eq53 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1100 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X3 (M.op X1 X2)) (M.op (M.op X3 X0) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X2 X0)) X3 (M.op X1 X2) X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X3 (M.op X1 X2)) (M.op X0 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X1 (M.op X2 X3)) X0) X3 (M.op X1 X2) X4
       have i₂ := eq53 X3 X1 X2 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 X2) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X2 X1
       have i₂ := eq642 X0 X2 X1
       grind)
    | exact superpose eq642 eq53
    | exact resolve eq53 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1123 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X2 X3 (M.op X2 (M.op (M.op X3 X1) X0))
       have i₂ := eq9 X0 X2 (M.op X3 X1)
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 (M.op X2 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq568 X1 X2 (M.op (M.op X1 (M.op X2 X2)) X0)
       have i₂ := eq53 X2 X1 X2 X0
       grind)
    | exact superpose eq53 eq568
    | exact resolve eq568 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq1140 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op (M.op (M.op X2 X3) (M.op (M.op X2 (M.op X3 X1)) X0)) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X4 X1 (M.op (M.op X2 X3) (M.op (M.op X2 (M.op X3 X1)) X0))
       have i₂ := eq53 X1 X2 X3 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1155 : ∀ X0 X1 X2 : G, (M.op x (M.op y X0)) = (M.op (M.op X1 X2) (M.op (M.op X1 (M.op X2 (M.op x y))) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq218 (M.op (M.op X1 X2) (M.op (M.op X1 (M.op X2 sF0)) x))
       have i₂ := eq53 sF0 X1 X2 x
       grind)
    | exact superpose eq53 eq218
    | exact resolve eq218 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op (M.op X2 (M.op X3 (M.op (M.op X2 (M.op X3 X1)) X0))) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1140 X0 X1 X2 X3 X4
       have i₂ := eq767 (M.op (M.op X2 (M.op X3 X1)) X0) X2 X3 X4
       grind)
    | exact superpose eq767 eq1140
    | exact resolve eq1140 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1192 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) X0)) (M.op (M.op X3 (M.op X1 X2)) (M.op X0 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1110 X0 X1 X2 X3 X4
       have i₂ := eq767 X0 X1 (M.op X2 X3) (M.op (M.op X3 (M.op X1 X2)) (M.op X0 X4))
       grind)
    | exact superpose eq767 eq1110
    | exact resolve eq1110 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1219 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X3 (M.op (M.op X2 (M.op X3 X1)) X0)) (M.op (M.op X1 X2) X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1168 X0 X1 X2 X3 X4
       have i₂ := eq1123 X4 (M.op X3 (M.op (M.op X2 (M.op X3 X1)) X0)) X1 X2
       grind)
    | (have i₁ := eq1168 X0 X1 X2 X3 X0
       have i₂ := eq1123 X0 X1 X2 (M.op X3 (M.op (M.op X2 (M.op X3 X1)) X0))
       grind)
    | exact superpose eq1123 eq1168
    | exact resolve eq1168 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1250 : ∀ X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X2 (M.op X3 X1)) (M.op (M.op X1 X2) X4))) = X4 := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1219 x X1 X2 X3 X4
       have i₂ := eq865 (M.op (M.op X1 X2) X4) x X3 (M.op X2 (M.op X3 X1))
       grind)
    | exact superpose eq865 eq1219
    | exact resolve eq1219 eq865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865 eq1219
  have eq1279 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op (M.op X2 X3) (M.op (M.op X2 (M.op X3 X1)) X0)) X4)) = (M.op (M.op X5 X0) (M.op X5 X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 X5 X1 (M.op (M.op X2 X3) (M.op (M.op X2 (M.op X3 X1)) X0))
       have i₂ := eq53 X1 X2 X3 X0
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1285 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op X3 X2) X4)) = (M.op (M.op X5 (M.op X0 (M.op X1 X2))) (M.op X5 X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 X5 (M.op X3 (M.op X0 X1)) (M.op X3 X2)
       have i₂ := eq55 X2 X3 X0 X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1287 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op y (M.op (M.op x y) X0)) X1)) = (M.op (M.op X2 X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq218 eq55
    | exact resolve eq55 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1289 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X1)) = (M.op (M.op X2 X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq241 eq55
    | exact resolve eq55 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op (M.op X2 X0) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq168 eq55
    | exact resolve eq55 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1293 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op X1 X2) (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X3 X2 (M.op X1 X2) (M.op X1 X0)
       have i₂ := eq392 X2 X1 X0
       grind)
    | exact superpose eq392 eq55
    | exact resolve eq55 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1302 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op y (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq218 eq55
    | exact resolve eq55 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1304 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq167 eq55
    | exact resolve eq55 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq1305 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq168 eq55
    | exact resolve eq55 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1307 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op (M.op X3 X4) (M.op X3 X0)))) = (M.op (M.op X4 (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X3 X4) (M.op X3 X0)) X4 X1 X2
       have i₂ := eq392 X4 X3 X0
       grind)
    | exact superpose eq392 eq55
    | exact resolve eq55 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq1314 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X3 X4) (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X3 (M.op X4 X0)) (M.op X3 X4) X1 X2
       have i₂ := eq9 X0 X3 X4
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1315 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X2))) = (M.op (M.op (M.op X5 (M.op X0 X1)) (M.op X3 X4)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 (M.op X5 X2) (M.op X5 (M.op X0 X1)) X3 X4
       have i₂ := eq55 X2 X5 X0 X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1317 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op y (M.op (M.op x y) X0)))) = (M.op (M.op x (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq218 eq55
    | exact resolve eq55 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1319 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) = (M.op (M.op (σ x) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq241 eq55
    | exact resolve eq55 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1321 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)))) = (M.op (M.op (σ y) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq168 eq55
    | exact resolve eq55 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq1329 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X1 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq642 X0 X1 (M.op X1 X2)
       have i₂ := eq55 X2 X1 X1 X0
       grind)
    | exact superpose eq55 eq642
    | exact resolve eq642 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1331 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op (M.op X3 X0) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X3 X0 (M.op X3 X2)
       have i₂ := eq55 X2 X3 X0 X1
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1346 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X0 X1)) X4) = (M.op (M.op (M.op X3 X2) (M.op X0 (M.op X1 X2))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq390 (M.op X3 X2) (M.op X3 (M.op X0 X1)) X4
       have i₂ := eq55 X2 X3 X0 X1
       grind)
    | exact superpose eq55 eq390
    | exact resolve eq390 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq1350 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op (M.op (M.op X3 (M.op X0 X1)) (M.op X0 (M.op X1 X2))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq642 (M.op X3 X2) (M.op X3 (M.op X0 X1)) X4
       have i₂ := eq55 X2 X3 X0 X1
       grind)
    | exact superpose eq55 eq642
    | exact resolve eq642 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq1351 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op (M.op X3 (M.op (M.op X0 X1) (M.op X0 (M.op X1 X2)))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1350 X0 X1 X2 X3 X4
       have i₂ := eq767 (M.op X0 (M.op X1 X2)) X3 (M.op X0 X1) X4
       grind)
    | exact superpose eq767 eq1350
    | exact resolve eq1350 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq1353 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X0 X1)) X4) = (M.op (M.op X3 (M.op X2 (M.op X0 (M.op X1 X2)))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1346 X0 X1 X2 X3 X4
       have i₂ := eq767 (M.op X0 (M.op X1 X2)) X3 X2 X4
       grind)
    | exact superpose eq767 eq1346
    | exact resolve eq1346 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1367 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op X3 (M.op (M.op X3 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq617 X0 X1 X2 X3
       have i₂ := eq1329 (M.op X3 X2) X3 X0
       grind)
    | (have i₁ := eq617 X0 X1 X2 X3
       have i₂ := eq1329 X3 (M.op X3 X2) X0
       grind)
    | exact superpose eq1329 eq617
    | exact resolve eq617 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq1372 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X0 X1 X2 X3
       have i₂ := eq1329 (M.op X1 (M.op X2 X3)) X1 X0
       grind)
    | (have i₁ := eq55 X0 X1 X2 X3
       have i₂ := eq1329 X1 (M.op X1 (M.op X2 X3)) X0
       grind)
    | exact superpose eq1329 eq55
    | exact resolve eq55 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1375 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op X1 (M.op (M.op X1 (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 x X1
       have i₂ := eq1329 (M.op X1 sF0) X1 x
       grind)
    | (have i₁ := eq80 x X0
       have i₂ := eq1329 X0 (M.op X0 sF0) x
       grind)
    | exact superpose eq1329 eq80
    | exact resolve eq80 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1380 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op X0 (M.op (M.op X3 X0) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1331 X0 X1 X2 X3
       have i₂ := eq1329 (M.op X3 X0) X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq1331 X0 X1 X2 X3
       have i₂ := eq1329 X0 (M.op X3 X0) (M.op X1 X2)
       grind)
    | exact superpose eq1329 eq1331
    | exact resolve eq1331 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq1400 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ y) X1) X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq631 x X1
       have i₂ := eq1329 sF4 sF2 x
       grind)
    | (have i₁ := eq631 x X1
       have i₂ := eq1329 sF2 sF4 x
       grind)
    | exact superpose eq1329 eq631
    | exact resolve eq631 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq1408 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op X1 X2)) X0) = (M.op X1 (M.op X2 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1321 X2 X1 X2
       have i₂ := eq1329 sF4 sF2 X2
       grind)
    | (have i₁ := eq1321 X2 X1 X2
       have i₂ := eq1329 sF2 sF4 X2
       grind)
    | exact superpose eq1329 eq1321
    | exact resolve eq1321 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1410 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq1319 eq777
    | exact resolve eq777 eq1319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq1419 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op y (M.op X0 (M.op y (M.op (M.op x y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1
       have i₂ := eq1317 X1 y X0
       grind)
    | exact superpose eq1317 eq772
    | exact resolve eq772 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq1420 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op y (M.op X0 (M.op y (M.op (M.op x y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq1317 X1 y X0
       grind)
    | exact superpose eq1317 eq380
    | exact resolve eq380 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq1422 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op y (M.op (M.op y X0) (M.op y (M.op (M.op x y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1014 X0 X1
       have i₂ := eq1317 X1 y (M.op y X0)
       grind)
    | exact superpose eq1317 eq1014
    | exact resolve eq1014 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1423 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op x y) (M.op X0 (M.op y (M.op (M.op x y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1061 x X0
       have i₂ := eq1317 X0 sF0 x
       grind)
    | exact superpose eq1317 eq1061
    | exact resolve eq1061 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1061 eq1317
  have eq1426 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X2))) = (M.op (M.op X5 (M.op (M.op X0 X1) (M.op X3 X4))) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1315 X0 X1 X2 X3 X4 X5
       have i₂ := eq767 (M.op X3 X4) X5 (M.op X0 X1) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq767 eq1315
    | exact resolve eq1315 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1427 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 (M.op X1 X2))) X0) = (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1314 X0 X1 X2 X3 X4
       have i₂ := eq767 (M.op X1 X2) X3 X4 X0
       grind)
    | exact superpose eq767 eq1314
    | exact resolve eq1314 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1432 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 X2)) X0) = (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X3 X4) X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1307 X0 X1 X2 X3 X4
       have i₂ := eq1329 (M.op X3 X4) X3 X0
       grind)
    | (have i₁ := eq1307 X0 X1 X2 X3 X4
       have i₂ := eq1329 X3 (M.op X3 X4) X0
       grind)
    | exact superpose eq1329 eq1307
    | exact resolve eq1307 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq1437 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 (M.op (M.op y (M.op x y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1302 X1 X0
       have i₂ := eq1123 X0 X1 y sF0
       grind)
    | (have i₁ := eq1302 x X0
       have i₂ := eq1123 X0 y sF0 x
       grind)
    | exact superpose eq1123 eq1302
    | exact resolve eq1302 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1450 : ∀ X0 X2 : G, (M.op x (M.op y X0)) = (M.op (M.op X2 (M.op x y)) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq1155 x x X2
       have i₂ := eq1293 (M.op X2 sF0) x X2 x
       grind)
    | exact superpose eq1293 eq1155
    | exact resolve eq1155 eq1293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq1293
  have eq1458 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1)) = (M.op X2 (M.op (M.op X2 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1291 X0 X1 X2
       have i₂ := eq1329 (M.op X2 X0) X2 X1
       grind)
    | (have i₁ := eq1291 X0 X1 X2
       have i₂ := eq1329 X2 (M.op X2 X0) X1
       grind)
    | exact superpose eq1329 eq1291
    | exact resolve eq1291 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1460 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X1)) = (M.op X2 (M.op (M.op X2 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1289 X0 X1 X2
       have i₂ := eq1329 (M.op X2 X0) X2 X1
       grind)
    | (have i₁ := eq1289 X0 X1 X2
       have i₂ := eq1329 X2 (M.op X2 X0) X1
       grind)
    | exact superpose eq1329 eq1289
    | exact resolve eq1289 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1462 : ∀ X0 X1 X2 : G, (M.op x (M.op (M.op y (M.op (M.op x y) X0)) X1)) = (M.op X2 (M.op (M.op X2 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1287 X0 X1 X2
       have i₂ := eq1329 (M.op X2 X0) X2 X1
       grind)
    | (have i₁ := eq1287 X0 X1 X2
       have i₂ := eq1329 X2 (M.op X2 X0) X1
       grind)
    | exact superpose eq1329 eq1287
    | exact resolve eq1287 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1464 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op X3 X2) X4)) = (M.op X5 (M.op (M.op X5 (M.op X0 (M.op X1 X2))) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1285 X0 X1 X2 X3 X4 X5
       have i₂ := eq1329 (M.op X5 (M.op X0 (M.op X1 X2))) X5 X4
       grind)
    | (have i₁ := eq1285 X0 X1 X2 X3 X4 X5
       have i₂ := eq1329 X5 (M.op X5 (M.op X0 (M.op X1 X2))) X4
       grind)
    | exact superpose eq1329 eq1285
    | exact resolve eq1285 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1470 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op (M.op X2 X3) (M.op (M.op X2 (M.op X3 X1)) X0)) X4)) = (M.op X5 (M.op (M.op X5 X0) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1279 X0 X1 X2 X3 X4 X5
       have i₂ := eq1329 (M.op X5 X0) X5 X4
       grind)
    | (have i₁ := eq1279 X0 X1 X2 X3 X4 X5
       have i₂ := eq1329 X5 (M.op X5 X0) X4
       grind)
    | exact superpose eq1329 eq1279
    | exact resolve eq1279 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1279
  have eq1473 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op (M.op X3 (M.op X0 (M.op (M.op X0 X1) (M.op X1 X2)))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1351 X0 X1 X2 X3 X4
       have i₂ := eq1329 (M.op X0 X1) X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq1351 X0 X1 X2 X3 X4
       have i₂ := eq1329 X0 (M.op X0 X1) (M.op X1 X2)
       grind)
    | exact superpose eq1329 eq1351
    | exact resolve eq1351 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351
  have eq1507 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq1408 eq774
    | exact resolve eq774 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774 eq1408
  have eq1521 : ∀ X0 X1 : G, (M.op x (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op x y) (M.op X1 (M.op y (M.op (M.op x y) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1032 X0 X1
       have i₂ := eq1423 X1 X0
       grind)
    | exact superpose eq1423 eq1032
    | exact resolve eq1032 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1524 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op y (M.op (M.op x y) (M.op X0 (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1422 X0 X1
       have i₂ := eq1423 X0 (M.op y (M.op sF0 X1))
       grind)
    | exact superpose eq1423 eq1422
    | exact resolve eq1422 eq1423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422 eq1423
  have eq1526 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op x (M.op y (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | exact superpose eq1420 eq768
    | exact resolve eq768 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq1527 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op X1 (M.op y (M.op X1 (M.op y (M.op (M.op x y) X0))))) := by
    intro X0 X1
    first
    | exact superpose eq1420 eq1375
    | exact resolve eq1375 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1530 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X2))) = (M.op X0 (M.op (M.op X5 (M.op (M.op X0 X1) (M.op X3 X4))) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1426 X0 X1 X2 X3 X4 X5
       have i₂ := eq1329 (M.op X5 (M.op (M.op X0 X1) (M.op X3 X4))) X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq1426 X0 X1 X2 X3 X4 X5
       have i₂ := eq1329 X0 (M.op X5 (M.op (M.op X0 X1) (M.op X3 X4))) (M.op X1 X2)
       grind)
    | exact superpose eq1329 eq1426
    | exact resolve eq1426 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1532 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 (M.op X1 (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq807 X0 X1 X2 X3
       have i₂ := eq1427 X3 X2 X0 X1 X2
       grind)
    | exact superpose eq1427 eq807
    | exact resolve eq807 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq1535 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X0 (M.op X2 (M.op X1 (M.op X2 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq711 X0 X1 X2 X3
       have i₂ := eq1427 X3 X0 X2 X1 X2
       grind)
    | exact superpose eq1427 eq711
    | exact resolve eq711 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq1536 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X2 (M.op X0 (M.op X0 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq822 X0 X1 X2 X3
       have i₂ := eq1427 X3 X2 X0 X0 X1
       grind)
    | exact superpose eq1427 eq822
    | exact resolve eq822 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq1541 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X0 X1)) X4) = (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X2 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1353 X0 X1 X2 X3 X4
       have i₂ := eq1427 X4 X0 (M.op X1 X2) X3 X2
       grind)
    | exact superpose eq1427 eq1353
    | exact resolve eq1353 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1353
  have eq1544 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X3 (M.op X2 (M.op X3 (M.op (M.op X2 (M.op X0 X1)) X4)))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1098 X0 X1 X2 X3 X4
       have i₂ := eq1427 (M.op (M.op X2 (M.op X0 X1)) X4) X0 X3 X2 X3
       grind)
    | exact superpose eq1427 eq1098
    | exact resolve eq1098 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098
  have eq1550 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 (M.op y (M.op y (M.op y (M.op (M.op x y) X1))))) := by
    intro X0 X1
    first
    | exact superpose eq1420 eq1437
    | exact resolve eq1437 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1437
  have eq1562 : ∀ X0 X2 : G, (M.op x (M.op y X0)) = (M.op y (M.op X2 (M.op y (M.op (M.op x y) (M.op X2 X0))))) := by
    intro X0 X2
    first
    | exact superpose eq1420 eq1450
    | exact resolve eq1450 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420 eq1450
  have eq1570 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op (M.op (σ x) X0) (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1458 X0 X0 X2
       have i₂ := eq1123 X0 (M.op sF2 X0) sF3 sF4
       grind)
    | (have i₁ := eq1458 X0 X0 X2
       have i₂ := eq1123 X0 sF3 sF4 (M.op sF2 X0)
       grind)
    | exact superpose eq1123 eq1458
    | exact resolve eq1458 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458
  have eq1572 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1460 X0 X0 X2
       have i₂ := eq1123 X0 (M.op sF4 X0) sF2 sF3
       grind)
    | (have i₁ := eq1460 X0 X0 X2
       have i₂ := eq1123 X0 sF2 sF3 (M.op sF4 X0)
       grind)
    | exact superpose eq1123 eq1460
    | exact resolve eq1460 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1460
  have eq1574 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1462 X0 X0 X2
       have i₂ := eq1123 X0 (M.op sF0 X0) x y
       grind)
    | (have i₁ := eq1462 X0 X0 X2
       have i₂ := eq1123 X0 x y (M.op sF0 X0)
       grind)
    | exact superpose eq1123 eq1462
    | exact resolve eq1462 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1576 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op X3 X2) X4)) = (M.op X0 (M.op (M.op X1 X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1464 X0 X1 X2 X3 X4 x
       have i₂ := eq1372 X4 x X0 (M.op X1 X2)
       grind)
    | exact superpose eq1372 eq1464
    | exact resolve eq1464 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq1582 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op (M.op X5 X0) X4)) = (M.op (M.op (M.op X2 (M.op X3 X1)) X0) (M.op (M.op X1 (M.op X2 X3)) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1470 X0 X1 X2 X3 X4 X5
       have i₂ := eq1123 X4 (M.op (M.op X2 (M.op X3 X1)) X0) X1 (M.op X2 X3)
       grind)
    | (have i₁ := eq1470 X0 X1 X2 X3 X0 X5
       have i₂ := eq1123 X0 X1 (M.op X2 X3) (M.op (M.op X2 (M.op X3 X1)) X0)
       grind)
    | exact superpose eq1123 eq1470
    | exact resolve eq1470 eq1123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123 eq1470
  have eq1585 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X2) X4) = (M.op (M.op X0 X1) (M.op (M.op X1 X2) (M.op X3 (M.op X0 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1473 X0 X1 X2 X3 X4
       have i₂ := eq1427 X4 (M.op X0 X1) (M.op X1 X2) X3 X0
       grind)
    | exact superpose eq1427 eq1473
    | exact resolve eq1473 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1604 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1))))) := by
    intro X0 X1
    first
    | exact superpose eq1507 eq1305
    | exact resolve eq1305 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1606 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 X2) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1507 eq1319
    | exact resolve eq1319 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1618 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op y (M.op (M.op x y) (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1524 X0 X1
       have i₂ := eq1329 sF0 y (M.op sF0 X1)
       grind)
    | (have i₁ := eq1524 X0 X1
       have i₂ := eq1329 y sF0 (M.op sF0 X1)
       grind)
    | exact superpose eq1329 eq1524
    | exact resolve eq1524 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq1619 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op y (M.op y (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq1526 X0
       have i₂ := eq1329 y x (M.op y (M.op sF0 X0))
       grind)
    | (have i₁ := eq1526 X0
       have i₂ := eq1329 x y (M.op y (M.op sF0 X0))
       grind)
    | exact superpose eq1329 eq1526
    | exact resolve eq1526 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1622 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X2))) = (M.op X0 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X0 X1) (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1530 X0 X1 X2 X3 X4 X5
       have i₂ := eq1427 (M.op X1 X2) X3 X4 X5 (M.op X0 X1)
       grind)
    | exact superpose eq1427 eq1530
    | exact resolve eq1530 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427 eq1530
  have eq1640 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1507 eq1570
    | exact resolve eq1570 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1570
  have eq1641 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X1))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1410 eq1572
    | exact resolve eq1572 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410 eq1572
  have eq1642 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op y (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) X1))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1419 eq1574
    | exact resolve eq1574 eq1419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419 eq1574
  have eq1646 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 (M.op (M.op X5 X0) X4)) = (M.op (M.op X2 (M.op (M.op X3 X1) X0)) (M.op (M.op X1 (M.op X2 X3)) X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1582 X0 X1 X2 X3 X4 X5
       have i₂ := eq767 X0 X2 (M.op X3 X1) (M.op (M.op X1 (M.op X2 X3)) X4)
       grind)
    | exact superpose eq767 eq1582
    | exact resolve eq1582 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq1582
  have eq1658 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op X1 X2) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1606 X0 X1 X2
       have i₂ := eq1329 (M.op X1 X2) sF2 (M.op sF4 X0)
       grind)
    | (have i₁ := eq1606 X0 X1 X2
       have i₂ := eq1329 sF2 (M.op X1 X2) (M.op sF4 X0)
       grind)
    | exact superpose eq1329 eq1606
    | exact resolve eq1606 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq1659 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (σ y) (M.op (σ y) (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1))))) := by
    intro X0 X1
    first
    | exact superpose eq1304 eq1604
    | exact resolve eq1604 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1671 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X2))) = (M.op X0 (M.op X3 (M.op X4 (M.op X5 (M.op X1 (M.op (M.op X0 X1) X2)))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq1622 X0 X1 X2 X3 X4 X5
       have i₂ := eq1329 (M.op X0 X1) X1 X2
       grind)
    | (have i₁ := eq1622 X0 X1 X2 X3 X4 X5
       have i₂ := eq1329 X1 (M.op X0 X1) X2
       grind)
    | exact superpose eq1329 eq1622
    | exact resolve eq1622 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1622
  have eq1676 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1400 eq1640
    | exact resolve eq1640 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400 eq1640
  have eq1677 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1507 eq1641
    | exact resolve eq1641 eq1507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1507 eq1641
  have eq1678 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op y (M.op X0 (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) X1))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1642 X0 X1 X2
       have i₂ := eq1618 y X1
       grind)
    | exact superpose eq1618 eq1642
    | exact resolve eq1642 eq1618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq1642
  have eq1684 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 X2) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1658 X0 X1 X2
       have i₂ := eq1329 sF4 sF2 (M.op (M.op X1 X2) (M.op sF4 X0))
       grind)
    | (have i₁ := eq1658 X0 X1 X2
       have i₂ := eq1329 sF2 sF4 (M.op (M.op X1 X2) (M.op sF4 X0))
       grind)
    | exact superpose eq1329 eq1658
    | exact resolve eq1658 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq1692 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1367 X0 X1 X2 x
       have i₂ := eq1676 X2 X0 x
       grind)
    | exact superpose eq1676 eq1367
    | exact resolve eq1367 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1695 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 (M.op X1 X2)) X0) = (M.op X1 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X4 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1432 X0 X1 X2 x X4
       have i₂ := eq1676 X4 X0 x
       grind)
    | exact superpose eq1676 eq1432
    | exact resolve eq1432 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1698 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op (M.op X3 X1) X0)) (M.op (M.op X1 (M.op X2 X3)) X4)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1646 X0 X1 X2 X3 X4 x
       have i₂ := eq1676 X0 X4 x
       grind)
    | exact superpose eq1676 eq1646
    | exact resolve eq1646 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1701 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X2 X3) (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1372 X0 x X2 X3
       have i₂ := eq1676 (M.op X2 X3) X0 x
       grind)
    | exact superpose eq1676 eq1372
    | exact resolve eq1372 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372
  have eq1706 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1304 eq1677
    | exact resolve eq1677 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq1707 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op y (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1678 X0 X1 X2
       have i₂ := eq1532 sF0 y y (M.op y (M.op sF0 (M.op sF0 X1)))
       grind)
    | exact superpose eq1532 eq1678
    | exact resolve eq1678 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532 eq1678
  have eq1711 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 X2) X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1684 X2 X1 X2
       have i₂ := eq1329 (M.op X1 X2) sF4 X2
       grind)
    | (have i₁ := eq1684 X2 X1 X2
       have i₂ := eq1329 sF4 (M.op X1 X2) X2
       grind)
    | exact superpose eq1329 eq1684
    | exact resolve eq1684 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684
  have eq1718 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op X2 X3) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1701 X0 X2 X3
       have i₂ := eq1329 (M.op X2 X3) sF2 (M.op sF2 (M.op sF4 X0))
       grind)
    | (have i₁ := eq1701 X0 X2 X3
       have i₂ := eq1329 sF2 (M.op X2 X3) (M.op sF2 (M.op sF4 X0))
       grind)
    | exact superpose eq1329 eq1701
    | exact resolve eq1701 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701
  have eq1720 : ∀ X0 X4 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X0 X4)))))) = X4 := by
    intro X0 X4
    first
    | (have i₁ := eq1192 X0 x x x X4
       have i₂ := eq1698 X0 x x x (M.op X0 X4)
       grind)
    | exact superpose eq1698 eq1192
    | exact resolve eq1192 eq1698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192 eq1698
  have eq1728 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1137 X0 X1 X2
       have i₂ := eq1695 X0 X2 X2 X1
       grind)
    | exact superpose eq1695 eq1137
    | exact resolve eq1137 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137
  have eq1730 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq375 X0 X1 X2 X3
       have i₂ := eq1695 X3 X2 X0 X1
       grind)
    | exact superpose eq1695 eq375
    | exact resolve eq375 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq1739 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X2 X4)))) = (M.op X0 (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X4))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1541 X0 X1 X2 X3 X4
       have i₂ := eq1695 X4 X0 X1 X3
       grind)
    | exact superpose eq1695 eq1541
    | exact resolve eq1541 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1541
  have eq1741 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X0 (M.op X3 (M.op X2 (M.op X3 (M.op X0 (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X4)))))))))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1544 X0 X1 X2 X3 X4
       have i₂ := eq1695 X4 X0 X1 X2
       grind)
    | exact superpose eq1695 eq1544
    | exact resolve eq1544 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1544
  have eq1744 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op X2 X1) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq761 X0 X1 X2 X3
       have i₂ := eq1695 X3 (M.op X2 X1) X0 X1
       grind)
    | exact superpose eq1695 eq761
    | exact resolve eq761 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq1748 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X4)) = (M.op X0 (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 X2) X4)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1576 X0 X1 X2 X3 X4
       have i₂ := eq1695 (M.op (M.op X3 X2) X4) X0 X1 X3
       grind)
    | exact superpose eq1695 eq1576
    | exact resolve eq1576 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576
  have eq1749 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 X0) X4))))))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1100 X0 X1 X2 X3 X4
       have i₂ := eq1695 (M.op (M.op X3 X0) X4) X1 X2 X3
       grind)
    | exact superpose eq1695 eq1100
    | exact resolve eq1100 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1750 : ∀ X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X2 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 X2) X4))))))))) = X4 := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1250 X1 X2 X3 X4
       have i₂ := eq1695 (M.op (M.op X1 X2) X4) X3 X1 X2
       grind)
    | exact superpose eq1695 eq1250
    | exact resolve eq1250 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq1756 : ∀ X0 X2 X3 X4 X5 : G, (M.op X3 (M.op X4 (M.op X5 X2))) = (M.op X0 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X2))))))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq1671 X0 x X2 X3 X4 X5
       have i₂ := eq1692 X2 x X0
       grind)
    | exact superpose eq1692 eq1671
    | exact resolve eq1671 eq1692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671
  have eq1760 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X1 X2))))))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1380 x X1 X2 X3
       have i₂ := eq1692 (M.op X1 X2) x X3
       grind)
    | exact superpose eq1692 eq1380
    | exact resolve eq1380 eq1692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1380
  have eq1763 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X2 X0) X1)) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ y) (M.op (σ y) X1))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1659 eq1706
    | exact resolve eq1706 eq1659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659 eq1706
  have eq1764 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1))))) = (M.op y (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1707 X0 X1 x
       have i₂ := eq1676 X0 X1 x
       grind)
    | exact superpose eq1676 eq1707
    | exact resolve eq1707 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq1766 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (M.op X1 X2) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1304 eq1711
    | exact resolve eq1711 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711
  have eq1772 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X2 X3) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1718 X0 X2 X3
       have i₂ := eq1329 sF4 sF2 (M.op (M.op X2 X3) (M.op sF2 (M.op sF4 X0)))
       grind)
    | (have i₁ := eq1718 X0 X2 X3
       have i₂ := eq1329 sF2 sF4 (M.op (M.op X2 X3) (M.op sF2 (M.op sF4 X0)))
       grind)
    | exact superpose eq1329 eq1718
    | exact resolve eq1718 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1773 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 X0) X4))))))))))))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1749 X2 X4 X1 X3 X4
       have i₂ := eq1695 (M.op X4 (M.op X1 (M.op sF4 (M.op X3 (M.op sF2 (M.op sF2 (M.op sF4 (M.op (M.op X3 X2) X4)))))))) X1 X2 X4
       grind)
    | exact superpose eq1695 eq1749
    | exact resolve eq1749 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749
  have eq1781 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X3))))))) = (M.op X1 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1730 X0 X1 X2 X3
       have i₂ := eq1695 X3 X1 X2 X0
       grind)
    | exact superpose eq1695 eq1730
    | exact resolve eq1730 eq1695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1791 : ∀ X0 X1 X3 X4 : G, (M.op X1 (M.op X0 (M.op X3 (M.op X3 (M.op X0 (M.op X1 X4)))))) = X4 := by
    intro X0 X1 X3 X4
    first
    | exact superpose eq1756 eq1741
    | exact resolve eq1741 eq1756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1741 eq1756
  have eq1793 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1))))) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ y) (M.op (σ y) X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1763 X0 X1 x
       have i₂ := eq1676 X0 X1 x
       grind)
    | exact superpose eq1676 eq1763
    | exact resolve eq1763 eq1676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676 eq1763
  have eq1796 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) X0)) = (M.op y (M.op X2 (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1764 eq1692
    | exact resolve eq1692 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq1799 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 (M.op X1 X2)) X0) = (M.op X1 (M.op X2 (M.op y (M.op X4 (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))))))) := by
    intro X0 X1 X2 X4
    first
    | exact superpose eq1764 eq1695
    | exact resolve eq1695 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1695
  have eq1801 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op y (M.op X1 (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1764 eq1728
    | exact resolve eq1728 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq1805 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X2 X4)))) = (M.op X0 (M.op X1 (M.op y (M.op X3 (M.op y (M.op (M.op x y) (M.op (M.op x y) X4))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1764 eq1739
    | exact resolve eq1739 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq1807 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op X2 X1) (M.op X0 (M.op y (M.op X1 (M.op y (M.op (M.op x y) (M.op (M.op x y) X3))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1764 eq1744
    | exact resolve eq1744 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq1809 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op y (M.op X3 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X1 X2))))))) := by
    intro X1 X2 X3
    first
    | exact superpose eq1764 eq1760
    | exact resolve eq1760 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1760
  have eq1812 : ∀ X0 X4 : G, (M.op y (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X4)))))) = X4 := by
    intro X0 X4
    first
    | exact superpose eq1764 eq1720
    | exact resolve eq1720 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720
  have eq1814 : ∀ X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op y (M.op X2 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 X2) X4))))))))) = X4 := by
    intro X1 X2 X3 X4
    first
    | exact superpose eq1764 eq1750
    | exact resolve eq1750 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750
  have eq1815 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X4)) = (M.op X0 (M.op X1 (M.op y (M.op X3 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X3 X2) X4)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1764 eq1748
    | exact resolve eq1748 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748
  have eq1825 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op X2 X3) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1772 X0 X2 X3
       have i₂ := eq1329 (M.op X2 X3) sF2 (M.op sF4 X0)
       grind)
    | (have i₁ := eq1772 X0 X2 X3
       have i₂ := eq1329 sF2 (M.op X2 X3) (M.op sF4 X0)
       grind)
    | exact superpose eq1329 eq1772
    | exact resolve eq1772 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq1826 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op y (M.op X1 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 X0) X4))))))))))))))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1764 eq1773
    | exact resolve eq1773 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773
  have eq1833 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X3))))))) = (M.op X1 (M.op X2 (M.op y (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) X3))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1764 eq1781
    | exact resolve eq1781 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1781
  have eq1843 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) X1))))) = (M.op (σ y) (M.op X0 (M.op (σ y) (M.op (σ y) (M.op (σ y) X1))))) := by
    intro X0 X1
    first
    | exact superpose eq1764 eq1793
    | exact resolve eq1793 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793
  have eq1851 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X2 X3) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1825 X0 X2 X3
       have i₂ := eq1329 sF4 sF2 (M.op (M.op X2 X3) (M.op sF4 X0))
       grind)
    | (have i₁ := eq1825 X0 X2 X3
       have i₂ := eq1329 sF2 sF4 (M.op (M.op X2 X3) (M.op sF4 X0))
       grind)
    | exact superpose eq1329 eq1825
    | exact resolve eq1825 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq1852 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X3 (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op X3 X0) X4))))))))) = X4 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1826 X0 x X2 X3 X4
       have i₂ := eq1812 X0 (M.op y (M.op x (M.op y (M.op sF0 (M.op sF0 (M.op x (M.op X2 (M.op sF4 (M.op X3 (M.op sF2 (M.op sF2 (M.op sF4 (M.op (M.op X3 X0) X4)))))))))))))
       grind)
    | exact superpose eq1812 eq1826
    | exact resolve eq1826 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq1859 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op y (M.op X1 (M.op y (M.op (M.op x y) (M.op (M.op x y) X3))))))) = (M.op X1 (M.op X2 (M.op y (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) X3))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1764 eq1833
    | exact resolve eq1833 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1871 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (M.op X2 X3) X0))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1851 X2 X2 X3
       have i₂ := eq1329 (M.op X2 X3) sF4 X2
       grind)
    | (have i₁ := eq1851 X2 X2 X3
       have i₂ := eq1329 sF4 (M.op X2 X3) X2
       grind)
    | exact superpose eq1329 eq1851
    | exact resolve eq1851 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851
  have eq1872 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X2 (M.op y (M.op X3 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X3 X0) X4))))))))) = X4 := by
    intro X0 X2 X3 X4
    first
    | exact superpose eq1764 eq1852
    | exact resolve eq1852 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764 eq1852
  have eq1884 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (M.op X2 X3) X0))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq1304 eq1871
    | exact resolve eq1871 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871
  have eq1892 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq1766 eq1884
    | exact resolve eq1884 eq1766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766 eq1884
  have eq1995 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 X1) (M.op X1 X0)) (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1122 X2 X3 (M.op X1 X0)
       have i₂ := eq787 X1 X0 (M.op X1 X0)
       grind)
    | (have i₁ := eq1122 X2 X3 (M.op X1 X0)
       have i₂ := eq787 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq787 eq1122
    | exact resolve eq1122 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq1996 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x (M.op (M.op x y) y)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq998 eq1122
    | exact resolve eq1122 eq998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq2021 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) (M.op y (M.op y (M.op x (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1996 X0 X1
       have i₂ := eq1799 (M.op X0 X1) sF0 y x
       grind)
    | exact superpose eq1799 eq1996
    | exact resolve eq1996 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996
  have eq2022 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op y (M.op (M.op X0 X1) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 X3))))))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1995 X0 X1 X2 X3
       have i₂ := eq1799 (M.op X2 X3) X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq1799 eq1995
    | exact resolve eq1995 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995
  have eq2027 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op (M.op x y) (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))))))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1859 eq2021
    | exact resolve eq2021 eq1859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021
  have eq2028 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op y (M.op y (M.op (M.op X0 X1) (M.op (M.op x y) (M.op (M.op x y) (M.op X2 X3))))))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2022 X0 X1 X2 X3
       have i₂ := eq1329 (M.op X0 X1) y (M.op sF0 (M.op sF0 (M.op X2 X3)))
       grind)
    | (have i₁ := eq2022 X0 X1 X2 X3
       have i₂ := eq1329 y (M.op X0 X1) (M.op sF0 (M.op sF0 (M.op X2 X3)))
       grind)
    | exact superpose eq1329 eq2022
    | exact resolve eq2022 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022
  have eq2032 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))))))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1859 eq2027
    | exact resolve eq2027 eq1859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859 eq2027
  have eq2033 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op X0 X1) (M.op (M.op x y) (M.op X2 X3))))))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2028 X0 X1 X2 X3
       have i₂ := eq1329 (M.op X0 X1) sF0 (M.op sF0 (M.op X2 X3))
       grind)
    | (have i₁ := eq2028 X0 X1 X2 X3
       have i₂ := eq1329 sF0 (M.op X0 X1) (M.op sF0 (M.op X2 X3))
       grind)
    | exact superpose eq1329 eq2028
    | exact resolve eq2028 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq2036 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))))))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2032 X0 X1
       have i₂ := eq1329 y x (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op X0 X1))))))
       grind)
    | (have i₁ := eq2032 X0 X1
       have i₂ := eq1329 x y (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op X0 X1))))))
       grind)
    | exact superpose eq1329 eq2032
    | exact resolve eq2032 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq2037 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X0 X1) (M.op X2 X3))))))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2033 X0 X1 X2 X3
       have i₂ := eq1329 (M.op X0 X1) sF0 (M.op X2 X3)
       grind)
    | (have i₁ := eq2033 X0 X1 X2 X3
       have i₂ := eq1329 sF0 (M.op X0 X1) (M.op X2 X3)
       grind)
    | exact superpose eq1329 eq2033
    | exact resolve eq2033 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033
  have eq2039 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1)))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1619 eq2036
    | exact resolve eq2036 eq1619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619 eq2036
  have eq2042 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq1304 eq241
    | exact resolve eq241 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq1304
  have eq2067 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op (σ y) (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op (σ y) X0)))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq2042 eq1892
    | exact resolve eq1892 eq2042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892 eq2042
  have eq2098 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op y (M.op (σ x) (M.op y (M.op (M.op x y) (M.op (M.op x y) X0)))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq1843 eq2067
    | exact resolve eq2067 eq1843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843 eq2067
  have eq2127 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op y (M.op y (M.op (σ x) (M.op (M.op x y) (M.op (M.op x y) X0)))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2098 X0 X2 X3
       have i₂ := eq1329 sF2 y (M.op sF0 (M.op sF0 X0))
       grind)
    | (have i₁ := eq2098 X0 X2 X3
       have i₂ := eq1329 y sF2 (M.op sF0 (M.op sF0 X0))
       grind)
    | exact superpose eq1329 eq2098
    | exact resolve eq2098 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098
  have eq2148 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (σ x) (M.op (M.op x y) X0)))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2127 X0 X2 X3
       have i₂ := eq1329 sF2 sF0 (M.op sF0 X0)
       grind)
    | (have i₁ := eq2127 X0 X2 X3
       have i₂ := eq1329 sF0 sF2 (M.op sF0 X0)
       grind)
    | exact superpose eq1329 eq2127
    | exact resolve eq2127 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2165 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) X0)))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2148 X2 X2 X3
       have i₂ := eq1329 sF2 sF0 X2
       grind)
    | (have i₁ := eq2148 X2 X2 X3
       have i₂ := eq1329 sF0 sF2 X2
       grind)
    | exact superpose eq1329 eq2148
    | exact resolve eq2148 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq2243 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X2 (M.op (M.op X3 X3) (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1329 X1 X2 (M.op (M.op X3 X3) (M.op X1 X0))
       have i₂ := eq1122 X1 X0 X3
       grind)
    | exact superpose eq1122 eq1329
    | exact resolve eq1329 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2245 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X1 (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1329 X1 X3 (M.op X0 X2)
       have i₂ := eq1329 X1 X0 X2
       grind)
    | (have i₁ := eq1329 X1 X3 (M.op X0 X2)
       have i₂ := eq1329 X0 X1 X2
       grind)
    | exact superpose eq1329 eq1329
    | exact resolve eq1329 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2248 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq1329 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1329
    | (have j0 := eq1329 X0 x y
       grind)
    | exact resolve eq1329 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2251 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq1329
    | (have j0 := eq1329 X0 (σ x) (σ y)
       grind)
    | exact resolve eq1329 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2269 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1122 X1 X2 X0
       have i₂ := eq1329 X1 (M.op X0 X0) (M.op X1 X2)
       grind)
    | (have i₁ := eq1122 X1 X2 X0
       have i₂ := eq1329 (M.op X0 X0) X1 (M.op X1 X2)
       grind)
    | exact superpose eq1329 eq1122
    | exact resolve eq1122 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2278 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op X1 (M.op (M.op X3 X3) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1122 X1 (M.op X0 X2) X3
       have i₂ := eq1329 X1 X0 X2
       grind)
    | (have i₁ := eq1122 X1 (M.op X0 X2) X3
       have i₂ := eq1329 X0 X1 X2
       grind)
    | exact superpose eq1329 eq1122
    | exact resolve eq1122 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2279 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1122 X0 X2 X1
       have i₂ := eq1329 (M.op X1 X1) X0 X2
       grind)
    | (have i₁ := eq1122 X0 X2 X1
       have i₂ := eq1329 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq1329 eq1122
    | exact resolve eq1122 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq2282 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op y (M.op X0 (M.op (M.op x y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq218 (M.op X1 x)
       have i₂ := eq1329 sF0 X1 x
       grind)
    | (have i₁ := eq218 (M.op X0 x)
       have i₂ := eq1329 X0 sF0 x
       grind)
    | exact superpose eq1329 eq218
    | exact resolve eq218 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2310 : (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) = (σ (M.op x (M.op x (M.op y y)))) := by
    first
    | exact superpose eq2248 eq1076
    | exact resolve eq1076 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq2313 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op y (M.op X3 (M.op y (M.op (M.op x y) (M.op (M.op x y) X4))))))) = (M.op X0 (M.op X2 (M.op (M.op X1 X2) (M.op X3 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1805 X0 X1 X2 X3 X4
       have i₂ := eq2245 X3 X2 X4 (M.op X1 X2)
       grind)
    | (have i₁ := eq1805 X0 X1 X0 X3 X2
       have i₂ := eq2245 X0 (M.op X1 X0) X2 X3
       grind)
    | exact superpose eq2245 eq1805
    | exact resolve eq1805 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1805
  have eq2316 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op y (M.op (M.op X2 X1) (M.op X0 (M.op X1 (M.op y (M.op (M.op x y) (M.op (M.op x y) X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1807 X0 X1 X2 X3
       have i₂ := eq2245 X0 y (M.op X1 (M.op y (M.op sF0 (M.op sF0 X3)))) (M.op X2 X1)
       grind)
    | (have i₁ := eq1807 X3 X1 X2 X3
       have i₂ := eq2245 y (M.op X2 X1) (M.op X1 (M.op y (M.op sF0 (M.op sF0 X3)))) X3
       grind)
    | exact superpose eq2245 eq1807
    | exact resolve eq1807 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq2319 : ∀ X0 X1 : G, (M.op x (M.op (M.op x y) X0)) = (M.op X1 (M.op y (M.op (M.op x y) (M.op X1 (M.op (M.op x y) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1521 X0 X0
       have i₂ := eq2245 X0 y (M.op sF0 X0) sF0
       grind)
    | (have i₁ := eq1521 X0 x
       have i₂ := eq2245 y sF0 (M.op sF0 X0) x
       grind)
    | exact superpose eq2245 eq1521
    | exact resolve eq1521 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1521
  have eq2357 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op y (M.op X1 (M.op (M.op X2 X1) (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2316 X0 X1 X2 X3
       have i₂ := eq2245 X0 X1 (M.op y (M.op sF0 (M.op sF0 X3))) (M.op X2 X1)
       grind)
    | (have i₁ := eq2316 X3 X0 X2 X3
       have i₂ := eq2245 X0 (M.op X2 X0) (M.op y (M.op sF0 (M.op sF0 X3))) X3
       grind)
    | exact superpose eq2245 eq2316
    | exact resolve eq2316 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2316
  have eq2360 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 (M.op y (M.op X3 (M.op y (M.op (M.op x y) (M.op (M.op x y) X4))))))) = (M.op X0 (M.op y (M.op X1 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X3 X4))))))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2313 X0 X1 x X3 X4
       have i₂ := eq1796 (M.op X3 X4) x X1
       grind)
    | exact superpose eq1796 eq2313
    | exact resolve eq2313 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2313
  have eq2375 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op y (M.op y (M.op X2 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) X3)))))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2357 X0 x X2 X3
       have i₂ := eq1796 (M.op X0 (M.op y (M.op sF0 (M.op sF0 X3)))) x X2
       grind)
    | exact superpose eq1796 eq2357
    | exact resolve eq2357 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796 eq2357
  have eq2387 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op y (M.op y (M.op X2 (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X3)))))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2375 X0 X2 X3
       have i₂ := eq2245 X0 y (M.op sF0 (M.op sF0 X3)) sF0
       grind)
    | (have i₁ := eq2375 X3 X2 X3
       have i₂ := eq2245 y sF0 (M.op sF0 (M.op sF0 X3)) X3
       grind)
    | exact superpose eq2245 eq2375
    | exact resolve eq2375 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2397 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op y (M.op y (M.op X2 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X3)))))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2387 X0 X2 X3
       have i₂ := eq2245 sF0 y (M.op sF0 (M.op X0 (M.op sF0 (M.op sF0 X3)))) y
       grind)
    | (have i₁ := eq2387 X0 X2 X3
       have i₂ := eq2245 y y (M.op sF0 (M.op X0 (M.op sF0 (M.op sF0 X3)))) sF0
       grind)
    | exact superpose eq2245 eq2387
    | exact resolve eq2387 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq2411 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op (M.op x y) X2)))))))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2279 X0 X1 X2
       have i₂ := eq2397 X1 X1 X2
       grind)
    | exact superpose eq2397 eq2279
    | exact resolve eq2279 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2279
  have eq2424 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 (M.op X1 X3)))) = (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X3)))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1536 X0 X1 X2 X3
       have i₂ := eq2397 X2 X1 X3
       grind)
    | exact superpose eq2397 eq1536
    | exact resolve eq1536 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq2425 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) (M.op X3 (M.op X0 X4)))) = (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1585 X0 X1 X2 X3 X4
       have i₂ := eq2397 X2 X3 X4
       grind)
    | exact superpose eq2397 eq1585
    | exact resolve eq1585 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585
  have eq2430 : ∀ X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op y (M.op X2 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))))))))))) = X4 := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1814 X1 X2 X3 X4
       have i₂ := eq2397 X2 X1 X4
       grind)
    | exact superpose eq2397 eq1814
    | exact resolve eq1814 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq2431 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X4)) = (M.op X0 (M.op X1 (M.op y (M.op X3 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4))))))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1815 X0 X1 X2 X3 X4
       have i₂ := eq2397 X2 X3 X4
       grind)
    | exact superpose eq2397 eq1815
    | exact resolve eq1815 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq2433 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X2 (M.op y (M.op X3 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))))))))))) = X4 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1872 X0 X2 X3 X4
       have i₂ := eq2397 X0 X3 X4
       grind)
    | exact superpose eq2397 eq1872
    | exact resolve eq1872 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872
  have eq2443 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op y (M.op X4 (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))))))) = (M.op y (M.op y (M.op X4 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 X2) (M.op (M.op x y) (M.op (M.op x y) X0)))))))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1799 X0 X1 X2 X4
       have i₂ := eq2397 (M.op X1 X2) X4 X0
       grind)
    | exact superpose eq2397 eq1799
    | exact resolve eq1799 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq2444 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op X1 (M.op X2 (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op (M.op x y) (M.op (M.op x y) (M.op X1 X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2243 X0 X1 X2 X3
       have i₂ := eq2397 X3 X3 (M.op X1 X0)
       grind)
    | exact superpose eq2397 eq2243
    | exact resolve eq2243 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2243
  have eq2448 : ∀ X0 X1 X2 X3 : G, (M.op X0 X2) = (M.op X1 (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op X1 X2))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2278 X0 X1 X2 X3
       have i₂ := eq2397 X3 X3 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq2397 eq2278
    | exact resolve eq2278 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278
  have eq2449 : ∀ X0 X1 X2 : G, (M.op y (M.op y (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op X1 X2)))))))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2269 X0 X1 X2
       have i₂ := eq2397 X0 X0 (M.op X1 (M.op X1 X2))
       grind)
    | exact superpose eq2397 eq2269
    | exact resolve eq2269 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269
  have eq2453 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op y (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op X2 X3)))))))))))))))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2037 X0 X1 X2 X3
       have i₂ := eq2397 X1 X0 (M.op X2 X3)
       grind)
    | exact superpose eq2397 eq2037
    | exact resolve eq2037 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037
  have eq2466 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op X2 X3)))))))))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2453 X0 X1 X2 X3
       have i₂ := eq1791 y y sF0 (M.op X0 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X1 (M.op sF0 (M.op sF0 (M.op X2 X3)))))))))
       grind)
    | (have i₁ := eq2453 X0 X1 X2 X3
       have i₂ := eq1791 X0 X1 X3 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op y (M.op X0 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X1 (M.op sF0 (M.op sF0 (M.op X2 X3)))))))))))))))
       grind)
    | exact superpose eq1791 eq2453
    | exact resolve eq2453 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791 eq2453
  have eq2468 : ∀ X1 X2 : G, (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op X1 X2)))))) = X2 := by
    intro X1 X2
    first
    | exact superpose eq2039 eq2449
    | exact resolve eq2449 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq2469 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op X1 X2))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2039 eq2448
    | exact resolve eq2448 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq2473 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X2 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X1 X0))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2039 eq2444
    | exact resolve eq2444 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2444
  have eq2474 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op y (M.op X4 (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))))))) = (M.op y (M.op y (M.op X4 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 X2) (M.op (M.op x y) X0)))))))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2443 X0 X1 X2 X4
       have i₂ := eq2245 (M.op X1 X2) sF0 (M.op sF0 X0) sF0
       grind)
    | (have i₁ := eq2443 X0 X1 X2 X4
       have i₂ := eq2245 sF0 sF0 (M.op sF0 X0) (M.op X1 X2)
       grind)
    | exact superpose eq2245 eq2443
    | exact resolve eq2443 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2443
  have eq2482 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X2 (M.op X3 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))))))))))) = X4 := by
    intro X0 X2 X3 X4
    first
    | exact superpose eq2360 eq2433
    | exact resolve eq2433 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2433
  have eq2484 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X4)) = (M.op X0 (M.op X1 (M.op X3 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4))))))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq2360 eq2431
    | exact resolve eq2431 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2431
  have eq2485 : ∀ X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op X2 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))))))))))) = X4 := by
    intro X1 X2 X3 X4
    first
    | exact superpose eq2360 eq2430
    | exact resolve eq2430 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430
  have eq2487 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op y (M.op y (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 X2) (M.op X3 (M.op X0 X4))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2425 X0 X1 X2 X3 X4
       have i₂ := eq2397 X1 X0 (M.op (M.op X1 X2) (M.op X3 (M.op X0 X4)))
       grind)
    | exact superpose eq2397 eq2425
    | exact resolve eq2425 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2425
  have eq2505 : ∀ X0 X2 : G, (M.op X0 (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) X2)))))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq2039 eq2411
    | exact resolve eq2411 eq2039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2039 eq2411
  have eq2522 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op y (M.op X4 (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))))))) = (M.op y (M.op y (M.op X4 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op X1 X2) X0)))))))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2474 X2 X1 X2 X4
       have i₂ := eq2245 (M.op X1 X2) sF0 X2 sF0
       grind)
    | (have i₁ := eq2474 X2 X1 X2 X4
       have i₂ := eq2245 sF0 sF0 X2 (M.op X1 X2)
       grind)
    | exact superpose eq2245 eq2474
    | exact resolve eq2474 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq2527 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X2 (M.op X3 (M.op x (M.op (M.op x y) (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X4))))))))))))))) = X4 := by
    intro X0 X2 X3 X4
    first
    | exact superpose eq1550 eq2482
    | exact resolve eq2482 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2482
  have eq2529 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X4)) = (M.op X0 (M.op X1 (M.op X3 (M.op x (M.op (M.op x y) (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq1550 eq2484
    | exact resolve eq2484 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2484
  have eq2530 : ∀ X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4))))))))))))))) = X4 := by
    intro X1 X2 X3 X4
    first
    | exact superpose eq1550 eq2485
    | exact resolve eq2485 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq2485
  have eq2532 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op y (M.op y (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4)))))))))))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2487 X0 X1 X2 X3 X4
       have i₂ := eq2397 X2 X1 (M.op X3 (M.op X0 X4))
       grind)
    | exact superpose eq2397 eq2487
    | exact resolve eq2487 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487
  have eq2546 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op X2 X3)))))) = X3 := by
    intro X1 X2 X3
    first
    | exact superpose eq2505 eq2466
    | exact resolve eq2466 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466
  have eq2560 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op y (M.op X4 (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))))))) = (M.op y (M.op y (M.op X4 (M.op (M.op X1 X2) X0)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2522 X0 X1 X2 X4
       have i₂ := eq2468 X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op sF0 (M.op sF0 (M.op (M.op X1 X2) X0)))))))
       grind)
    | exact superpose eq2468 eq2522
    | exact resolve eq2522 eq2468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468 eq2522
  have eq2565 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X2 (M.op X3 (M.op y (M.op x (M.op (M.op x y) (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X4))))))))))))))) = X4 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2527 X0 X2 X3 X4
       have i₂ := eq2245 sF0 y (M.op X3 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X0 (M.op sF0 (M.op sF0 X4)))))))) x
       grind)
    | (have i₁ := eq2527 X0 X2 X3 X4
       have i₂ := eq2245 y x (M.op X3 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X0 (M.op sF0 (M.op sF0 X4)))))))) sF0
       grind)
    | exact superpose eq2245 eq2527
    | exact resolve eq2527 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq2567 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X4)) = (M.op X0 (M.op X1 (M.op X3 (M.op y (M.op x (M.op (M.op x y) (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2529 X0 X1 X2 X3 X4
       have i₂ := eq2245 sF0 y (M.op X3 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 X4)))))))) x
       grind)
    | (have i₁ := eq2529 X0 X1 X2 X3 X4
       have i₂ := eq2245 y x (M.op X3 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 X4)))))))) sF0
       grind)
    | exact superpose eq2245 eq2529
    | exact resolve eq2529 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529
  have eq2568 : ∀ X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op X2 (M.op y (M.op x (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4))))))))))))))) = X4 := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq2530 X1 X2 X3 X4
       have i₂ := eq2245 sF0 y (M.op X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 X4)))))))) x
       grind)
    | (have i₁ := eq2530 X1 X2 X3 X4
       have i₂ := eq2245 y x (M.op X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 X4)))))))) sF0
       grind)
    | exact superpose eq2245 eq2530
    | exact resolve eq2530 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2530
  have eq2570 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op y (M.op y (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X1 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4)))))))))))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2532 X0 X1 X2 X3 X4
       have i₂ := eq2245 sF0 y (M.op y (M.op X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4))))))))))) sF0
       grind)
    | (have i₁ := eq2532 X0 X1 X2 X3 X4
       have i₂ := eq2245 y sF0 (M.op y (M.op X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4))))))))))) sF0
       grind)
    | exact superpose eq2245 eq2532
    | exact resolve eq2532 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2532
  have eq2595 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op y (M.op X4 (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))))))) = (M.op y (M.op y (M.op X4 (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X0))))))))))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2560 X0 X1 X2 X4
       have i₂ := eq2397 X2 X1 X0
       grind)
    | exact superpose eq2397 eq2560
    | exact resolve eq2560 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq2600 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X2 (M.op X3 (M.op x (M.op y (M.op (M.op x y) (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X4))))))))))))))) = X4 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2565 X0 X2 X3 X4
       have i₂ := eq1329 y x (M.op sF0 (M.op X3 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X0 (M.op sF0 (M.op sF0 X4)))))))))
       grind)
    | (have i₁ := eq2565 X0 X2 X3 X4
       have i₂ := eq1329 x y (M.op sF0 (M.op X3 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X0 (M.op sF0 (M.op sF0 X4)))))))))
       grind)
    | exact superpose eq1329 eq2565
    | exact resolve eq2565 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq2602 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X4)) = (M.op X0 (M.op X1 (M.op X3 (M.op x (M.op y (M.op (M.op x y) (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2567 X0 X1 X2 X3 X4
       have i₂ := eq1329 y x (M.op sF0 (M.op X3 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 X4)))))))))
       grind)
    | (have i₁ := eq2567 X0 X1 X2 X3 X4
       have i₂ := eq1329 x y (M.op sF0 (M.op X3 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 X4)))))))))
       grind)
    | exact superpose eq1329 eq2567
    | exact resolve eq2567 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2567
  have eq2603 : ∀ X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op X2 (M.op x (M.op y (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4))))))))))))))) = X4 := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq2568 X1 X2 X3 X4
       have i₂ := eq1329 y x (M.op sF0 (M.op X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 X4)))))))))
       grind)
    | (have i₁ := eq2568 X1 X2 X3 X4
       have i₂ := eq1329 x y (M.op sF0 (M.op X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 X4)))))))))
       grind)
    | exact superpose eq1329 eq2568
    | exact resolve eq2568 eq1329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568
  have eq2605 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op y (M.op y (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4)))))))))))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2570 X0 X0 X2 X3 X4
       have i₂ := eq2245 X0 y (M.op sF0 (M.op sF0 (M.op y (M.op X0 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4))))))))))))) sF0
       grind)
    | (have i₁ := eq2570 X0 X3 X2 X3 X4
       have i₂ := eq2245 y sF0 (M.op sF0 (M.op sF0 (M.op y (M.op X3 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4))))))))))))) X3
       grind)
    | exact superpose eq2245 eq2570
    | exact resolve eq2570 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570
  have eq2631 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X0 (M.op X2 (M.op X3 (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))))) = X4 := by
    intro X0 X2 X3 X4
    first
    | exact superpose eq218 eq2600
    | exact resolve eq2600 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600
  have eq2633 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X4)) = (M.op X0 (M.op X1 (M.op X3 (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq218 eq2602
    | exact resolve eq2602 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602
  have eq2634 : ∀ X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op X2 (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))))) = X4 := by
    intro X1 X2 X3 X4
    first
    | exact superpose eq218 eq2603
    | exact resolve eq2603 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2636 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op y (M.op y (M.op X0 (M.op x (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4))))))))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq2319 eq2605
    | exact resolve eq2605 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319 eq2605
  have eq2661 : ∀ X0 X2 X4 : G, (M.op X2 (M.op X0 (M.op X2 (M.op X0 (M.op (M.op x y) (M.op (M.op x y) X4)))))) = X4 := by
    intro X0 X2 X4
    first
    | (have i₁ := eq2631 X0 X2 x X4
       have i₂ := eq2505 X0 (M.op x (M.op x (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X0 (M.op sF0 (M.op sF0 X4)))))))))
       grind)
    | exact superpose eq2505 eq2631
    | exact resolve eq2631 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq2663 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X2) X4)) = (M.op X0 (M.op X1 (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2633 X0 X1 X2 x X4
       have i₂ := eq2505 X0 (M.op x (M.op x (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 X4)))))))))
       grind)
    | exact superpose eq2505 eq2633
    | exact resolve eq2633 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505 eq2633
  have eq2664 : ∀ X1 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op X1 (M.op (M.op x y) (M.op (M.op x y) X4)))))) = X4 := by
    intro X1 X3 X4
    first
    | exact superpose eq2473 eq2634
    | exact resolve eq2634 eq2473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473 eq2634
  have eq2666 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op y (M.op x (M.op y (M.op X0 (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4))))))))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2636 X0 X1 X2 X3 X4
       have i₂ := eq2245 X0 x (M.op sF0 (M.op X1 (M.op sF0 (M.op sF0 (M.op y (M.op X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4))))))))))))))) y
       grind)
    | (have i₁ := eq2636 X3 X1 X2 X3 X4
       have i₂ := eq2245 x y (M.op sF0 (M.op X1 (M.op sF0 (M.op sF0 (M.op y (M.op X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X3 X4))))))))))))))) X3
       grind)
    | exact superpose eq2245 eq2636
    | exact resolve eq2636 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2636
  have eq2690 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4))))))))))) = (M.op X0 (M.op X1 (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4))))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq2663 X0 X1 X2 X4
       have i₂ := eq2397 X2 X1 X4
       grind)
    | exact superpose eq2397 eq2663
    | exact resolve eq2663 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2663
  have eq2692 : ∀ X0 X1 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op x (M.op y (M.op y (M.op X0 (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4))))))))))))))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2666 X0 X1 X2 X3 X4
       have i₂ := eq2245 x y (M.op X0 (M.op sF0 (M.op X1 (M.op sF0 (M.op sF0 (M.op y (M.op X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4)))))))))))))))) y
       grind)
    | (have i₁ := eq2666 X0 X1 X2 X3 X4
       have i₂ := eq2245 y y (M.op X0 (M.op sF0 (M.op X1 (M.op sF0 (M.op sF0 (M.op y (M.op X1 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4)))))))))))))))) x
       grind)
    | exact superpose eq2245 eq2666
    | exact resolve eq2666 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2666
  have eq2716 : ∀ X0 X1 X2 X4 : G, (M.op X1 (M.op X2 (M.op y (M.op X4 (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))))))) = (M.op y (M.op y (M.op X4 (M.op X1 (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X0))))))) := by
    intro X0 X1 X2 X4
    first
    | exact superpose eq2690 eq2595
    | exact resolve eq2595 eq2690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595 eq2690
  have eq2721 : ∀ X0 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op x (M.op y (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4))))))))))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2692 X0 x X2 X3 X4
       have i₂ := eq1535 sF0 x y (M.op y (M.op sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4))))))))
       grind)
    | exact superpose eq1535 eq2692
    | exact resolve eq2692 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535 eq2692
  have eq2743 : ∀ X0 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op x (M.op y (M.op y (M.op X0 (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4))))))))))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2721 X0 X2 X3 X4
       have i₂ := eq2245 y sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4)))))) sF0
       grind)
    | (have i₁ := eq2721 X0 X2 X3 X4
       have i₂ := eq2245 sF0 sF0 (M.op sF0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4)))))) y
       grind)
    | exact superpose eq2245 eq2721
    | exact resolve eq2721 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2721
  have eq2898 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op x (M.op X1 (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1329 x X1 (M.op X0 y)
       have i₂ := eq2248 X0
       grind)
    | (have i₁ := eq1329 X0 X1 (M.op x y)
       have i₂ := eq2248 X0
       grind)
    | exact superpose eq2248 eq1329
    | exact resolve eq1329 eq2248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2912 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (M.op X1 (M.op (σ x) (M.op X0 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq2251 eq1329
    | exact resolve eq1329 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2918 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ x) (M.op X1 (M.op X0 (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq2251 eq1329
    | exact resolve eq1329 eq2251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5156 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (σ x) (M.op X3 (M.op X0 (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) X2))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2165 eq1329
    | exact resolve eq1329 eq2165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq368
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq368
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq368 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6447 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6437
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6437
    | exact resolve eq6437 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6437
  have eq6448 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6447
    | exact resolve eq6447 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6447
  have eq6449 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6448
       have r₂ := eq27
       grind)
    | exact resolve eq6448 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6448
  have eq6450 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6449
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6449
    | exact resolve eq6449 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6449
  have eq6451 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6450
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6450
    | exact resolve eq6450 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6450
  have eq6452 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6451 eq143
    | (have r₁ := eq143
       have r₂ := eq6451
       grind)
    | exact resolve eq143 eq6451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq6451
  have eq6464 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq6452
  have eq6465 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq6464
  have eq6469 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6465
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq6465
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq6465 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6465
  have eq6479 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6469
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6469
    | exact resolve eq6469 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6469
  have eq6480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6479
    | exact resolve eq6479 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6479
  have eq6481 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6480
       have r₂ := eq27
       grind)
    | exact resolve eq6480 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6480
  have eq6482 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6481
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6481
    | exact resolve eq6481 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6481
  have eq6483 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6482
  have eq6484 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6483
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6483
    | exact resolve eq6483 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6483
  have eq6485 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6484
  have eq6486 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq135
       have i₂ := eq6485
       grind)
    | exact superpose eq6485 eq135
    | (have r₁ := eq135
       have r₂ := eq6485
       grind)
    | exact resolve eq135 eq6485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq6488 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq155 x
       have i₂ := eq6485
       grind)
    | exact superpose eq6485 eq155
    | exact resolve eq155 eq6485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6485
  have eq6497 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6486
  have eq6498 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6497
  have eq6500 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6488
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6488
    | exact resolve eq6488 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6488
  have eq6501 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq6500
    | exact resolve eq6500 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6500
  have eq7287 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq368
       have i₂ := eq6498
       grind)
    | exact superpose eq6498 eq368
    | exact resolve eq368 eq6498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq6498
  have eq7291 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7287
  have eq7294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq7291
    | exact resolve eq7291 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7291
  have eq7296 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7294
       have r₂ := eq27
       grind)
    | exact resolve eq7294 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7294
  have eq7324 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7296 eq6501
    | exact resolve eq6501 eq7296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6501 eq7296
  have eq7339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7324
  have eq7344 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7339
       have r₂ := eq27
       grind)
    | exact resolve eq7339 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7339
  have eq7348 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7344 eq2251
    | exact resolve eq2251 eq7344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251 eq7344
  have eq7447 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (M.op X1 (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq7348 eq2912
    | exact resolve eq2912 eq7348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2912 eq7348
  have eq8154 : ∀ X0 : G, (M.op (τ (M.op X0 (σ x))) (τ (M.op X0 (σ x)))) = (τ (M.op X0 (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7447 eq473
    | exact resolve eq473 eq7447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7447
  have eq8187 : ∀ X0 : G, (M.op (τ (M.op X0 (σ x))) (τ (M.op X0 (σ x)))) = (τ (M.op (σ x) (M.op X0 (M.op (M.op X0 (σ x)) (σ y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2918 eq8154
    | exact resolve eq8154 eq2918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2918 eq8154
  have eq8214 : ∀ X0 : G, (M.op (τ (M.op X0 (σ x))) (τ (M.op X0 (σ x)))) = (τ (M.op (σ x) (M.op X0 (M.op y (M.op y (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (M.op (M.op x y) (M.op (M.op x y) (σ y)))))))))))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8187 x
       have i₂ := eq2397 sF2 x sF3
       grind)
    | exact superpose eq2397 eq8187
    | exact resolve eq8187 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8187
  have eq8233 : ∀ X0 : G, (M.op (τ (M.op X0 (σ x))) (τ (M.op X0 (σ x)))) = (τ (M.op y (M.op (σ x) (M.op X0 (M.op y (M.op X0 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (σ x) (M.op (M.op x y) (M.op (M.op x y) (σ y)))))))))))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8214 X0
       have i₂ := eq2245 X0 y (M.op y (M.op X0 (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op sF2 (M.op sF0 (M.op sF0 sF3))))))))) sF2
       grind)
    | (have i₁ := eq8214 x
       have i₂ := eq2245 y sF2 (M.op y (M.op x (M.op y (M.op y (M.op sF0 (M.op sF0 (M.op sF2 (M.op sF0 (M.op sF0 sF3))))))))) x
       grind)
    | exact superpose eq2245 eq8214
    | exact resolve eq8214 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8214
  have eq8249 : ∀ X0 : G, (M.op (τ (M.op X0 (σ x))) (τ (M.op X0 (σ x)))) = (τ (M.op y (M.op X0 (M.op y (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (σ y)))))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5156 eq8233
    | exact resolve eq8233 eq5156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5156 eq8233
  have eq8264 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (M.op X0 (σ x))) (τ (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8249 X0
       have i₂ := eq2661 X0 x (M.op y (M.op X0 (M.op y (M.op X0 (M.op sF0 (M.op sF0 sF3))))))
       grind)
    | exact superpose eq2661 eq8249
    | exact resolve eq8249 eq2661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8249
  have eq8278 : ∀ X0 : G, y = (M.op (τ (M.op X0 (σ x))) (τ (M.op X0 (σ x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq39 eq8264
    | exact resolve eq8264 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq8264
  have eq8402 : y = (M.op (M.op (τ (σ x)) (τ (σ x))) (M.op (τ (σ x)) (τ (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8278 sF2
       have i₂ := eq473 sF2
       grind)
    | exact superpose eq473 eq8278
    | exact resolve eq8278 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq8278
  have eq8422 : y = (M.op y (M.op y (M.op (τ (σ x)) (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (τ (σ x))))))))))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8402
       have i₂ := eq2397 (τ sF2) (τ sF2) (M.op (τ sF2) (τ sF2))
       grind)
    | exact superpose eq2397 eq8402
    | exact resolve eq8402 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8402
  have eq8425 : y = (M.op y (M.op y (M.op y (M.op (τ (σ x)) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (τ (σ x))))))))))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2716 eq8422
    | exact resolve eq8422 eq2716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8422
  have eq8428 : y = (M.op y (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (M.op (τ (σ x)) (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (τ (σ x))))))))))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2360 eq8425
    | exact resolve eq8425 eq2360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360 eq8425
  have eq8430 : y = (M.op x (M.op y (M.op (M.op x y) (M.op (τ (σ x)) (M.op (τ (σ x)) (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (τ (σ x)))))))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1527 eq8428
    | exact resolve eq8428 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527 eq8428
  have eq8432 : y = (M.op (τ (σ x)) (M.op (τ (σ x)) (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (τ (σ x))))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq218 eq8430
    | exact resolve eq8430 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8430
  have eq8434 : y = (M.op (M.op x y) (M.op (τ (σ x)) (M.op (τ (σ x)) (M.op (M.op x y) (M.op (τ (σ x)) (τ (σ x))))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8432
       have i₂ := eq2245 (τ sF2) sF0 (M.op sF0 (M.op (τ sF2) (τ sF2))) (τ sF2)
       grind)
    | (have i₁ := eq8432
       have i₂ := eq2245 sF0 (τ sF2) (M.op sF0 (M.op (τ sF2) (τ sF2))) (τ sF2)
       grind)
    | exact superpose eq2245 eq8432
    | exact resolve eq8432 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8432
  have eq8435 : y = (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (τ (σ x))))))))))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8434
       have i₂ := eq2424 (τ sF2) sF0 sF0 (M.op (τ sF2) (τ sF2))
       grind)
    | exact superpose eq2424 eq8434
    | exact resolve eq8434 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8434
  have eq8436 : y = (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (τ (σ x))))))))))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2716 eq8435
    | exact resolve eq8435 eq2716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716 eq8435
  have eq8437 : y = (M.op x (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (τ (σ x)))))))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1562 eq8436
    | exact resolve eq8436 eq1562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562 eq8436
  have eq8438 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (τ (σ x)) (τ (σ x))))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq218 eq8437
    | exact resolve eq8437 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8437
  have eq8439 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op x x))))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq8438
    | exact resolve eq8438 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq8438
  have eq8440 : y = (M.op (M.op x y) (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op (M.op x y) x))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8439
       have i₂ := eq2245 sF0 x x sF0
       grind)
    | (have i₁ := eq8439
       have i₂ := eq2245 x sF0 x sF0
       grind)
    | exact superpose eq2245 eq8439
    | exact resolve eq8439 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8439
  have eq8441 : y = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) x))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8440
       have i₂ := eq2245 sF0 x (M.op sF0 (M.op sF0 x)) sF0
       grind)
    | (have i₁ := eq8440
       have i₂ := eq2245 x sF0 (M.op sF0 (M.op sF0 x)) sF0
       grind)
    | exact superpose eq2245 eq8440
    | exact resolve eq8440 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8440
  have eq9832 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op (M.op x y) X0)))) := by
    intro X0
    first
    | exact superpose eq1812 eq218
    | exact resolve eq218 eq1812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812
  have eq9845 : ∀ X0 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op x (M.op y (M.op y (M.op X0 (M.op x (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4)))))))))) := by
    intro X0 X2 X3 X4
    first
    | exact superpose eq9832 eq2743
    | exact resolve eq2743 eq9832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2743 eq9832
  have eq9916 : ∀ X0 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op x (M.op y (M.op x (M.op y (M.op X0 (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4)))))))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq9845 X0 X2 X3 X4
       have i₂ := eq2245 X0 x (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4))))) y
       grind)
    | (have i₁ := eq9845 X3 X2 X3 X4
       have i₂ := eq2245 x y (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X3 X4))))) X3
       grind)
    | exact superpose eq2245 eq9845
    | exact resolve eq9845 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9845
  have eq9965 : ∀ X0 X2 X3 X4 : G, (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X4)))))))))) = (M.op x (M.op x (M.op y (M.op y (M.op X0 (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4)))))))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq9916 X0 X2 X3 X4
       have i₂ := eq2245 y x (M.op y (M.op X0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4))))))) x
       grind)
    | (have i₁ := eq9916 X0 X2 X3 X4
       have i₂ := eq2245 x x (M.op y (M.op X0 (M.op X2 (M.op sF0 (M.op sF0 (M.op X3 (M.op X0 X4))))))) y
       grind)
    | exact superpose eq2245 eq9916
    | exact resolve eq9916 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9916
  have eq12341 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq2661 eq2165
    | exact resolve eq2165 eq2661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2661
  have eq12900 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0 X1
    first
    | exact superpose eq2664 eq2165
    | exact resolve eq2165 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664
  have eq12931 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq12341 eq12900
    | exact resolve eq12900 eq12341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12341 eq12900
  have eq12988 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op y (M.op X1 (M.op y (M.op y (M.op y X0))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1801 X0 X1 X2
       have i₂ := eq12931 X0 sF0
       grind)
    | exact superpose eq12931 eq1801
    | exact resolve eq1801 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801
  have eq12999 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op y (M.op y (M.op X2 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X0 (M.op y (M.op y X3)))))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2397 X0 X2 X0
       have i₂ := eq12931 X0 sF0
       grind)
    | exact superpose eq12931 eq2397
    | exact resolve eq2397 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq13002 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 (M.op X1 X3)))) = (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op y (M.op y X3)))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2424 X0 X1 X2 X0
       have i₂ := eq12931 X0 sF0
       grind)
    | exact superpose eq12931 eq2424
    | exact resolve eq2424 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2424
  have eq13046 : ∀ X0 X2 X3 X4 : G, (M.op x (M.op x (M.op y (M.op y (M.op X0 (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4)))))))))) = (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op X2 (M.op y (M.op y X4)))))))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq9965 X0 X2 X3 X0
       have i₂ := eq12931 X0 sF0
       grind)
    | exact superpose eq12931 eq9965
    | exact resolve eq9965 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9965
  have eq13069 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op y (M.op X3 (M.op y (M.op y (M.op y (M.op X1 X2))))))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1809 X1 X2 X3
       have i₂ := eq12931 (M.op X1 X2) sF0
       grind)
    | exact superpose eq12931 eq1809
    | exact resolve eq1809 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq13073 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X1 (M.op y (M.op y (M.op X2 X3)))))) = X3 := by
    intro X1 X2 X3
    first
    | (have i₁ := eq2546 X1 X2 X3
       have i₂ := eq12931 (M.op X2 X3) sF0
       grind)
    | exact superpose eq12931 eq2546
    | exact resolve eq2546 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2546
  have eq13080 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op y (M.op y (M.op y (M.op y (M.op X0 (M.op X1 X2))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2469 X0 X1 X2
       have i₂ := eq12931 (M.op X0 (M.op X1 X2)) sF0
       grind)
    | exact superpose eq12931 eq2469
    | exact resolve eq2469 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2469
  have eq13136 : y = (M.op x (M.op y (M.op y (M.op (M.op x y) (M.op (M.op x y) x))))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8441
       have i₂ := eq12931 (M.op sF0 (M.op sF0 x)) sF0
       grind)
    | exact superpose eq12931 eq8441
    | exact resolve eq8441 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8441
  have eq13145 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ x) (M.op X2 (M.op X3 (M.op y (M.op y (M.op y (M.op y (M.op (σ x) X0)))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq2165 X0 X2 X3
       have i₂ := eq12931 (M.op sF2 X0) sF0
       grind)
    | exact superpose eq12931 eq2165
    | exact resolve eq2165 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165
  have eq13375 : y = (M.op y (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2282 eq13136
    | exact resolve eq13136 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13136
  have eq13426 : ∀ X0 X2 X3 X4 : G, (M.op x (M.op x (M.op y (M.op y (M.op X0 (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4)))))))))) = (M.op y (M.op y (M.op X3 (M.op y (M.op y (M.op y (M.op y (M.op X2 (M.op y (M.op y X4)))))))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq13046 X0 X2 X3 X4
       have i₂ := eq12931 (M.op X2 (M.op y (M.op y X4))) sF0
       grind)
    | exact superpose eq12931 eq13046
    | exact resolve eq13046 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13046
  have eq13468 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 (M.op X1 X3)))) = (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op y (M.op X2 (M.op y (M.op y X3)))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13002 X0 X1 X2 X3
       have i₂ := eq12931 (M.op X2 (M.op y (M.op y X3))) sF0
       grind)
    | exact superpose eq12931 eq13002
    | exact resolve eq13002 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13002
  have eq13471 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op y (M.op y (M.op X2 (M.op y (M.op y (M.op y (M.op y (M.op X0 (M.op y (M.op y X3)))))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq12999 X0 X2 X3
       have i₂ := eq12931 (M.op X0 (M.op y (M.op y X3))) sF0
       grind)
    | exact superpose eq12931 eq12999
    | exact resolve eq12999 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12999
  have eq13603 : ∀ X0 X2 X3 X4 : G, (M.op x (M.op x (M.op y (M.op y (M.op X0 (M.op X2 (M.op (M.op x y) (M.op (M.op x y) (M.op X3 (M.op X0 X4)))))))))) = (M.op X3 (M.op X2 (M.op y (M.op y X4)))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq13426 X0 X2 X3 X4
       have i₂ := eq13069 y (M.op X2 (M.op y (M.op y X4))) X3
       grind)
    | exact superpose eq13069 eq13426
    | exact resolve eq13426 eq13069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13426
  have eq13635 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 (M.op X1 X3)))) = (M.op X1 (M.op X2 (M.op y (M.op y X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13468 X0 X1 X2 X3
       have i₂ := eq13069 y (M.op X2 (M.op y (M.op y X3))) X1
       grind)
    | exact superpose eq13069 eq13468
    | exact resolve eq13468 eq13069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13468
  have eq13638 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op X2 (M.op X0 (M.op y (M.op y X3)))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq13471 X0 X2 X3
       have i₂ := eq13069 y (M.op X0 (M.op y (M.op y X3))) X2
       grind)
    | exact superpose eq13069 eq13471
    | exact resolve eq13471 eq13069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13069 eq13471
  have eq13701 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 (M.op y (M.op y X4)))) = (M.op x (M.op x (M.op y (M.op y (M.op X0 (M.op X2 (M.op y (M.op y (M.op X3 (M.op X0 X4)))))))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq13603 X0 X2 X3 X4
       have i₂ := eq12931 (M.op X3 (M.op X0 X4)) sF0
       grind)
    | exact superpose eq12931 eq13603
    | exact resolve eq13603 eq12931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12931 eq13603
  have eq13960 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13375 eq218
    | exact resolve eq218 eq13375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13375
  have eq13969 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13960
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13960
    | exact resolve eq13960 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq13960
  have eq13970 : x = (M.op x y) := by grind
  clear eq13969
  have eq13974 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq13970 eq20
    | exact resolve eq20 eq13970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq13986 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | exact superpose eq13970 eq218
    | exact resolve eq218 eq13970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq14002 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq13970 eq2248
    | exact resolve eq2248 eq13970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248
  have eq14004 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op y (M.op X0 (M.op x X1)))) := by
    intro X0 X1
    first
    | exact superpose eq13970 eq2282
    | exact resolve eq2282 eq13970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq14006 : (σ (M.op x (M.op x (M.op y y)))) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | exact superpose eq13970 eq2310
    | exact resolve eq2310 eq13970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq14013 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op X0 y))) = (M.op X1 (M.op X0 x)) := by
    intro X0 X1
    first
    | exact superpose eq13970 eq2898
    | exact resolve eq2898 eq13970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2898 eq13970
  have eq14457 : (σ (M.op x (M.op x (M.op y y)))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq14006
       have i₂ := eq155 x
       grind)
    | exact superpose eq155 eq14006
    | exact resolve eq14006 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155 eq14006
  have eq14459 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op x (M.op y (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14004 X0 X1
       have i₂ := eq2245 X0 x X1 y
       grind)
    | (have i₁ := eq14004 x x
       have i₂ := eq2245 x y x x
       grind)
    | exact superpose eq2245 eq14004
    | exact resolve eq14004 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14004
  have eq14473 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq13986 X0
       have i₂ := eq2245 y x X0 x
       grind)
    | (have i₁ := eq13986 x
       have i₂ := eq2245 x x x y
       grind)
    | exact superpose eq2245 eq13986
    | exact resolve eq13986 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13986
  have eq14500 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13974
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13974
    | exact resolve eq13974 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13974
  have eq14592 : (σ (M.op x (M.op x (M.op y y)))) = (M.op (σ x) (M.op (σ x) (M.op y (M.op y (M.op (σ x) (σ x)))))) := by
    first
    | (have i₁ := eq14457
       have i₂ := eq13638 (σ x) (σ x) (M.op (σ x) (σ x))
       grind)
    | exact superpose eq13638 eq14457
    | exact resolve eq14457 eq13638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13638 eq14457
  have eq14595 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X2 (M.op y (M.op y X4)))) = (M.op y (M.op X0 (M.op X2 (M.op y (M.op y (M.op X3 (M.op X0 X4))))))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq13701 X0 X2 X3 X4
       have i₂ := eq14459 y (M.op X0 (M.op X2 (M.op y (M.op y (M.op X3 (M.op X0 X4))))))
       grind)
    | exact superpose eq14459 eq13701
    | exact resolve eq13701 eq14459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13701 eq14459
  have eq14614 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq14500 eq22
    | exact resolve eq22 eq14500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq14615 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq14500 eq26
    | exact resolve eq26 eq14500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq14786 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (σ (M.op x y)) (M.op X2 (M.op X3 (M.op y (M.op y (M.op y (M.op y (M.op (σ (M.op x y)) X0)))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq14500 eq13145
    | exact resolve eq13145 eq14500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13145 eq14500
  have eq14933 : (σ (M.op x (M.op x (M.op y y)))) = (M.op y (M.op (σ x) (M.op (σ x) (M.op y (M.op (σ x) (σ x)))))) := by
    first
    | (have i₁ := eq14592
       have i₂ := eq2245 (σ x) y (M.op y (M.op (σ x) (σ x))) (σ x)
       grind)
    | (have i₁ := eq14592
       have i₂ := eq2245 y (σ x) (M.op y (M.op (σ x) (σ x))) (σ x)
       grind)
    | exact superpose eq2245 eq14592
    | exact resolve eq14592 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14592
  have eq15033 : (σ (M.op x (M.op x (M.op y y)))) = (M.op y (M.op y (M.op y (M.op y (M.op (σ x) (σ x)))))) := by
    first
    | (have i₁ := eq14933
       have i₂ := eq13635 (σ x) y y (M.op (σ x) (σ x))
       grind)
    | exact superpose eq13635 eq14933
    | exact resolve eq14933 eq13635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13635 eq14933
  have eq15090 : (σ (M.op x (M.op x (M.op y y)))) = (M.op y (M.op y (M.op y (M.op y (M.op (σ (M.op x y)) (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq15033
       have i₂ := eq14614
       grind)
    | exact superpose eq14614 eq15033
    | exact resolve eq15033 eq14614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14614 eq15033
  have eq15103 : (σ (M.op x (M.op y x))) = (M.op y (M.op y (M.op y (M.op y (M.op (σ (M.op x y)) (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq15090
       have i₂ := eq14013 y x
       grind)
    | exact superpose eq14013 eq15090
    | exact resolve eq15090 eq14013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14013 eq15090
  have eq15294 : y = (M.op x (M.op y x)) := by
    first
    | (have i₁ := eq14473 y
       have i₂ := eq14002 y
       grind)
    | exact superpose eq14002 eq14473
    | exact resolve eq14473 eq14002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14002 eq14473
  have eq15307 : (σ y) = (M.op y (M.op y (M.op y (M.op y (M.op (σ (M.op x y)) (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq15103
       have i₂ := eq15294
       grind)
    | exact superpose eq15294 eq15103
    | exact resolve eq15103 eq15294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15103 eq15294
  have eq15314 : (σ y) = (M.op y (M.op y (M.op y (M.op y (M.op (σ (M.op x y)) (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq15307
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15307
    | exact resolve eq15307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15307
  have eq15410 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (σ (M.op x y)) (M.op X1 (M.op y (M.op y (M.op y (M.op y (M.op (σ (M.op x y)) X2)))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq14786 eq1329
    | exact resolve eq1329 eq14786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329 eq14786
  have eq15418 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op y (M.op (σ (M.op x y)) (M.op X1 (M.op y (M.op y (M.op y (M.op (σ (M.op x y)) X2)))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15410 X0 X0 X2
       have i₂ := eq2245 X0 y (M.op y (M.op y (M.op y (M.op sF1 X2)))) sF1
       grind)
    | (have i₁ := eq15410 X0 x X2
       have i₂ := eq2245 y sF1 (M.op y (M.op y (M.op y (M.op sF1 X2)))) x
       grind)
    | exact superpose eq2245 eq15410
    | exact resolve eq15410 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245 eq15410
  have eq15428 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op y (M.op X1 (M.op y (M.op y X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15418 X0 y X2
       have i₂ := eq14595 X0 sF1 y (M.op y (M.op y (M.op sF1 X2)))
       grind)
    | (have i₁ := eq15418 X0 X2 x
       have i₂ := eq14595 sF1 X2 y x
       grind)
    | exact superpose eq14595 eq15418
    | exact resolve eq15418 eq14595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14595 eq15418
  have eq15437 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op y X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12988 X0 X1 X2
       have i₂ := eq15428 X2 X1 (M.op y X0)
       grind)
    | exact superpose eq15428 eq12988
    | exact resolve eq12988 eq15428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12988
  have eq15452 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 (M.op y (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13080 X0 X1 X2
       have i₂ := eq15428 X1 y (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq15428 eq13080
    | exact resolve eq13080 eq15428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13080 eq15428
  have eq15572 : (σ y) = (M.op y (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq15314
       have i₂ := eq15452 y y (M.op sF1 sF1)
       grind)
    | exact superpose eq15452 eq15314
    | exact resolve eq15314 eq15452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15314 eq15452
  have eq15621 : ∀ X2 X3 : G, (M.op X2 (M.op y (M.op X2 X3))) = X3 := by
    intro X2 X3
    first
    | (have i₁ := eq13073 x X2 X3
       have i₂ := eq15437 (M.op X2 X3) y x
       grind)
    | exact superpose eq15437 eq13073
    | exact resolve eq13073 eq15437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13073 eq15437
  have eq16047 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq15572 eq15621
    | exact resolve eq15621 eq15572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15572 eq15621
  have eq16062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14615 eq16047
    | exact resolve eq16047 eq14615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14615 eq16047
  have eq16068 : False := by grind
  exact eq16068
