import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1833`: `x = (x ◇ (x ◇ x)) ◇ (x ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation1833 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1833 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1833.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
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
    | (have r₁ := eq25 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq45 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq42 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq44 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq45 X1 X0
       grind)
    | (have r₁ := eq48 X1 X0
       have r₂ := eq45 X0 X1
       grind)
    | exact resolve eq48 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq48
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq57
  have eq110 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq110 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq110 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq110 X0 X0
       have r₂ := eq61 X0 X0
       grind)
    | exact resolve eq110 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq110
  have eq353 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq114 (σ X0) (σ X1)
       grind)
    | exact superpose eq114 eq15
    | exact resolve eq15 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 X1
       have i₂ := eq114 X0 X1
       grind)
    | exact superpose eq114 eq353
    | exact resolve eq353 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq353
  have eq360 : False := by grind
  exact eq360

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pxy_x_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
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
  have eq183 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq176 eq178
    | exact resolve eq178 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 X0 x X3
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq178 x x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq176 eq554
    | exact resolve eq554 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq554
  have eq590 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq175 eq553
    | exact resolve eq553 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq553
  have eq591 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1 x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq552
    | exact resolve eq552 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq614 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 x
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq591 x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq591
    | exact resolve eq591 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq998 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq1037 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq1044 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1047 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1056 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1037
       grind)
    | exact superpose eq1037 eq41
    | exact resolve eq41 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1057 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1056
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1056
    | exact resolve eq1056 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1059 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1057
    | exact resolve eq1057 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1059 eq1044
    | exact resolve eq1044 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq1059
  have eq1076 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1069
       have r₂ := eq27
       grind)
    | exact resolve eq1069 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq1081 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1076 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1076
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1076
       grind)
    | exact resolve eq13 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1100 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1081
  have eq1106 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1100 eq153
    | exact resolve eq153 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1100
  have eq1109 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq1106
    | exact resolve eq1106 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1106
  have eq1112 : y = (M.op y y) := by
    first
    | (have j1 := eq1047 y
       grind)
    | (have r₁ := eq1109
       have r₂ := eq1047 y
       grind)
    | exact resolve eq1109 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1116 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1112
       grind)
    | exact resolve eq13 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1 y
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq178
    | exact resolve eq178 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq183
    | exact resolve eq183 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1130 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq559 X0 X1 y
       have i₂ := eq1112
       grind)
    | exact superpose eq1112 eq559
    | exact resolve eq559 eq1112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq1112
  have eq1135 : y = (k y y) := by grind
  clear eq1116
  have eq1136 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1127
    | exact resolve eq1127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1140 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1135
       grind)
    | exact superpose eq1135 eq41
    | exact resolve eq41 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1135
  have eq1143 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1140
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1140
    | exact resolve eq1140 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1140
  have eq1147 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1136 eq590
    | exact resolve eq590 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq1136
  have eq1162 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1143 eq1047
    | (have j0 := eq1047 (σ y)
       grind)
    | (have r₁ := eq1047 (σ y)
       have r₂ := eq1143
       grind)
    | exact resolve eq1047 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143
  have eq1163 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1162
  have eq1170 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1147 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1212 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1163 eq178
    | exact resolve eq178 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1214 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1163 eq187
    | exact resolve eq187 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq1219 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1163 eq614
    | exact resolve eq614 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq1163
  have eq1224 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1214
    | exact resolve eq1214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214
  have eq1231 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1224 eq589
    | exact resolve eq589 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq1224
  have eq1268 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1231 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq1231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1439 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1219 eq16
    | exact resolve eq16 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1458 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) y) := by
    intro X0
    first
    | (have i₁ := eq1439 X0 x
       have i₂ := eq1130 (M.op (M.op X0 sF3) X0) x
       grind)
    | exact superpose eq1130 eq1439
    | exact resolve eq1439 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1439
  have eq1465 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq1219 eq1458
    | exact resolve eq1458 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq1458
  have eq3764 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1170 eq38
    | exact resolve eq38 eq1170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1170
  have eq3770 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3764
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3764
    | exact resolve eq3764 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3764
  have eq3888 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3770 eq998
    | (have j0 := eq998 X0 (σ x) x
       grind)
    | exact resolve eq998 eq3770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq3889 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3888 x
       have i₂ := eq1130 (M.op sF1 sF2) x
       grind)
    | exact superpose eq1130 eq3888
    | exact resolve eq3888 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq3888
  have eq3893 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3889
       have i₂ := eq1465 (M.op sF1 sF2)
       grind)
    | exact superpose eq1465 eq3889
    | exact resolve eq3889 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465 eq3889
  have eq3895 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq3893
    | (have j1 := eq28 x (σ x)
       grind)
    | exact resolve eq3893 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq3893
  have eq3896 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3770 eq3895
    | exact resolve eq3895 eq3770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770 eq3895
  have eq3897 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq3896
    | exact resolve eq3896 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3896
  have eq3898 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq3897
       have r₂ := eq27
       grind)
    | exact resolve eq3897 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897
  have eq3976 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3898 eq1212
    | exact resolve eq1212 eq3898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3979 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq3976
    | exact resolve eq3976 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq4007 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3898 eq3979
    | exact resolve eq3979 eq3898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898 eq3979
  have eq4062 : x ≠ x ∨ x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq4007
       grind)
    | exact superpose eq4007 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq4007
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4007
       grind)
    | exact resolve eq13 eq4007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4007
  have eq4073 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4062
  have eq4168 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4073
       grind)
    | exact superpose eq4073 eq40
    | exact resolve eq40 eq4073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4073
  have eq4175 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4168
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4168
    | exact resolve eq4168 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168
  have eq5137 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4175 eq1047
    | (have j0 := eq1047 (σ x)
       grind)
    | (have r₁ := eq1047 (σ x)
       have r₂ := eq4175
       grind)
    | exact resolve eq1047 eq4175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4175
  have eq5139 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5137
  have eq5329 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5139 eq1212
    | exact resolve eq1212 eq5139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq5332 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5329
    | exact resolve eq5329 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5329
  have eq5363 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5139 eq5332
    | exact resolve eq5332 eq5139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5139 eq5332
  have eq5364 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5363
  have eq5392 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5364 eq27
    | exact resolve eq27 eq5364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq5403 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5364 eq1268
    | (have r₁ := eq1268
       have r₂ := eq5364
       grind)
    | exact resolve eq1268 eq5364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268 eq5364
  have eq5411 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq5403
  have eq5567 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | exact superpose eq5411 eq142
    | exact resolve eq142 eq5411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq5411
  have eq5574 : x = (k x x) := by
    first
    | exact superpose eq30 eq5567
    | exact resolve eq5567 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5567
  have eq5756 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1047 x
       have i₂ := eq5574
       grind)
    | exact superpose eq5574 eq1047
    | (have j0 := eq1047 x
       grind)
    | (have r₁ := eq1047 x
       have r₂ := eq5574
       grind)
    | exact resolve eq1047 eq5574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq5574
  have eq5759 : x = (M.op x x) := by grind
  clear eq5756
  have eq5805 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1126 x x
       have i₂ := eq5759
       grind)
    | exact superpose eq5759 eq1126
    | exact resolve eq1126 eq5759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq5810 : x = (M.op x y) := by
    first
    | (have i₁ := eq5805
       have i₂ := eq5759
       grind)
    | exact superpose eq5759 eq5805
    | exact resolve eq5805 eq5759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5759 eq5805
  have eq5841 : x = (M.op x y) := by
    first
    | (have i₁ := eq5810
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5810
    | exact resolve eq5810 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5810
  have eq5890 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5841
       grind)
    | exact superpose eq5841 eq22
    | exact resolve eq22 eq5841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5841
  have eq5957 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5890 eq20
    | exact resolve eq20 eq5890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5890
  have eq5975 : False := by grind
  exact eq5975

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pxy_x_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
    | (have j0 := eq11 X1 X1
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
  clear eq40
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
  have eq182 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq548 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 X0 x X3
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq178 x x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X0 X1 x
       have i₂ := eq178 X0 X2 x
       grind)
    | (have i₁ := eq178 X1 X1 X1
       have i₂ := eq178 X1 X1 X2
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq585 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq175 eq548
    | exact resolve eq548 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq548
  have eq900 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq933 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq940 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq944 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq933
       grind)
    | exact superpose eq933 eq41
    | exact resolve eq41 eq933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq951 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq950
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq950
    | exact resolve eq950 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq953 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq951
    | exact resolve eq951 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq953 eq940
    | exact resolve eq940 eq953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq953
  have eq970 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq963
       have r₂ := eq27
       grind)
    | exact resolve eq963 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq975 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq970 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq970
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq970
       grind)
    | exact resolve eq13 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq992 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq975
  have eq998 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq992 eq153
    | exact resolve eq153 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq992
  have eq1001 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq998
    | exact resolve eq998 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq998
  have eq1004 : y = (M.op y y) := by
    first
    | (have j1 := eq944 y
       grind)
    | (have r₁ := eq1001
       have r₂ := eq944 y
       grind)
    | exact resolve eq1001 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1008 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1004
       grind)
    | exact resolve eq13 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1018 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq178
    | exact resolve eq178 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1019 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq182 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq182
    | exact resolve eq182 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq185 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq185
    | exact resolve eq185 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq554 X0 X1 y
       have i₂ := eq1004
       grind)
    | exact superpose eq1004 eq554
    | exact resolve eq554 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq1004
  have eq1025 : y = (k y y) := by grind
  clear eq1008
  have eq1026 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1019
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1019
    | exact resolve eq1019 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1019
  have eq1031 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1025
       grind)
    | exact superpose eq1025 eq41
    | exact resolve eq41 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1025
  have eq1034 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1031
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1031
    | exact resolve eq1031 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1031
  have eq1038 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1026 eq585
    | exact resolve eq585 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq1041 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1026 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1026
       grind)
    | exact resolve eq13 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1048 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  clear eq1041
  have eq1053 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1034 eq944
    | (have j0 := eq944 (σ y)
       grind)
    | (have r₁ := eq944 (σ y)
       have r₂ := eq1034
       grind)
    | exact resolve eq944 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1054 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1053
  have eq1112 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1054 eq185
    | exact resolve eq185 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq1054
  have eq1118 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1112
    | exact resolve eq1112 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1112
  have eq1237 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1020 eq1118
    | exact resolve eq1118 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq1118
  have eq1348 : x = (k (M.op x y) x) := by
    first
    | exact superpose eq1048 eq1038
    | exact resolve eq1038 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq1048
  have eq1446 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1348 eq38
    | exact resolve eq38 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1348
  have eq1451 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq1446
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1446
    | exact resolve eq1446 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1457 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq1451 eq900
    | (have j0 := eq900 X0 (σ x) x
       grind)
    | exact resolve eq900 eq1451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq1458 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1457 x
       have i₂ := eq1022 (M.op sF1 sF2) x
       grind)
    | exact superpose eq1022 eq1457
    | exact resolve eq1457 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022 eq1457
  have eq1462 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28 eq1458
    | (have j1 := eq28 x (σ x)
       grind)
    | exact resolve eq1458 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1458
  have eq1464 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1451 eq1462
    | exact resolve eq1462 eq1451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451 eq1462
  have eq1465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1237 eq1464
    | exact resolve eq1464 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq1466 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq1465
       have r₂ := eq27
       grind)
    | exact resolve eq1465 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1480 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1466 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1466
       grind)
    | exact resolve eq13 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1484 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq1466 eq562
    | exact resolve eq562 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1486 : (σ x) = (k (σ x) (σ x)) := by grind
  clear eq1480
  have eq1489 : (M.op (σ x) (σ x)) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq1484 x
       have i₂ := eq1018 sF2 x
       grind)
    | exact superpose eq1018 eq1484
    | exact resolve eq1484 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq1484
  have eq1499 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1237 eq1489
    | exact resolve eq1489 eq1237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1237 eq1489
  have eq1503 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1466 eq1499
    | exact resolve eq1499 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466 eq1499
  have eq1505 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1503 eq27
    | exact resolve eq27 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1503
  have eq1522 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | exact superpose eq1486 eq142
    | exact resolve eq142 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1486
  have eq1528 : x = (k x x) := by
    first
    | exact superpose eq30 eq1522
    | exact resolve eq1522 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1522
  have eq1598 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq944 x
       have i₂ := eq1528
       grind)
    | exact superpose eq1528 eq944
    | (have j0 := eq944 x
       grind)
    | (have r₁ := eq944 x
       have r₂ := eq1528
       grind)
    | exact resolve eq944 eq1528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq1528
  have eq1600 : x = (M.op x x) := by grind
  clear eq1598
  have eq1612 : (M.op x (M.op x y)) = (M.op x x) := by
    first
    | (have i₁ := eq182 x
       have i₂ := eq1600
       grind)
    | exact superpose eq1600 eq182
    | exact resolve eq182 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1635 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1612
       have i₂ := eq1600
       grind)
    | exact superpose eq1600 eq1612
    | exact resolve eq1612 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600 eq1612
  have eq1645 : x = (M.op x y) := by
    first
    | exact superpose eq1026 eq1635
    | exact resolve eq1635 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq1635
  have eq1654 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1645
       grind)
    | exact superpose eq1645 eq22
    | exact resolve eq22 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1645
  have eq1686 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1654 eq20
    | exact resolve eq20 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1654
  have eq1704 : False := by grind
  exact eq1704

/-- `Equation1874`: `x = (x ◇ (y ◇ z)) ◇ (y ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_pyy_pyx_Equation1874 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1874 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1874.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq52 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X2 X3)) X5)) = X1 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X1 (M.op X0 (M.op X2 X3)) (M.op X2 x) X5
       have i₂ := eq14 X0 X2 X3 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X4)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X4)) X1 x X2
       have i₂ := eq14 X0 X1 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq79 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
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
  have eq80 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
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
  have eq103 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq76
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq76 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq103
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
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
  have eq160 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq137 eq16
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x x (M.op x x)
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 X2 X6 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op X0 X2) X6)) := by
    intro X0 X1 X2 X6
    first
    | (have i₁ := eq53 X1 (M.op X0 X2) (M.op (M.op X2 (M.op x x)) x) X6
       have i₂ := eq52 X2 X0 x x x
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq580 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq549 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq549
    | (have j0 := eq549 y x
       grind)
    | exact resolve eq549 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq549
    | (have j0 := eq549 (σ y) (σ x)
       grind)
    | exact resolve eq549 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq987 : ∀ X0 X1 X2 X3 X4 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (M.op (σ X0) (M.op X2 X3)) X4)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (σ X0) (σ X1) X2 X3 X4
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq52
    | (have j1 := eq78 X0 X1
       grind)
    | exact resolve eq52 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq78
  have eq4087 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq79 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq79
    | (have j0 := eq79 x
       grind)
    | exact resolve eq79 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq4114 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4087
  have eq4124 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4114
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq4114
    | exact resolve eq4114 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq4114
  have eq4133 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4124
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq4124 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4124
  have eq4138 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4133 eq49
    | exact resolve eq49 eq4133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq4133
  have eq4196 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq80
    | (have j0 := eq80 y
       grind)
    | exact resolve eq80 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq4221 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4196
  have eq4229 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4221
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq4221
    | exact resolve eq4221 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq4221
  have eq4240 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4229
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4229 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4229
  have eq4248 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4240 eq108
    | exact resolve eq108 eq4240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq4415 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq138
    | (have j0 := eq138 (M.op x y)
       grind)
    | exact resolve eq138 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq4439 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq4415
  have eq4446 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq137 eq4439
    | exact resolve eq4439 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq4439
  have eq4459 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq4446
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4446 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4446
  have eq4469 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq4459 eq160
    | exact resolve eq160 eq4459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq4459
  have eq11879 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq987 X0 X1 x x x
       have i₂ := eq566 (σ X0) (σ (k X0 X1)) (M.op x x) x
       grind)
    | exact superpose eq566 eq987
    | (have j0 := eq987 X0 X1 x x x
       grind)
    | exact resolve eq987 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq987
  have eq17559 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17568 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq17559
    | exact resolve eq17559 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17559
  have eq17579 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq17568
       have r₂ := eq27
       grind)
    | exact resolve eq17568 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17568
  have eq17581 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq17579
    | exact resolve eq17579 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17579
  have eq17585 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17581 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17581
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17581
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17581
       grind)
    | exact resolve eq12 eq17581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17604 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17581 eq549
    | exact resolve eq549 eq17581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17581
  have eq17614 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq17585
  have eq17625 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq17614
    | exact resolve eq17614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17614
  have eq17626 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq17625
  have eq17629 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17604 eq4138
    | exact resolve eq4138 eq17604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17604
  have eq17692 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq17629
    | exact resolve eq17629 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17629
  have eq17716 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4240 eq109
    | exact resolve eq109 eq4240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq4240
  have eq19070 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq17626 eq102
    | exact resolve eq102 eq17626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq17626
  have eq19086 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19070
  have eq19097 : (τ (σ (M.op x y))) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19086 eq4138
    | exact resolve eq4138 eq19086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4138 eq19086
  have eq19162 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq19097
    | exact resolve eq19097 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19097
  have eq19567 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17692
       have i₂ := eq19162
       grind)
    | exact superpose eq19162 eq17692
    | exact resolve eq17692 eq19162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17692 eq19162
  have eq19586 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19567
  have eq19639 : x ≠ x ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19586
       grind)
    | exact superpose eq19586 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19586
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19586
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq19586
       grind)
    | exact resolve eq12 eq19586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19640 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19586
       grind)
    | exact superpose eq19586 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq19586
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19586
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19586
       grind)
    | exact resolve eq13 eq19586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19658 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq549 x y
       have i₂ := eq19586
       grind)
    | exact superpose eq19586 eq549
    | exact resolve eq549 eq19586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19586
  have eq19667 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19640
  have eq19668 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq19639
  have eq19679 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19667
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19667
    | exact resolve eq19667 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19667
  have eq19680 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19668
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19668
    | exact resolve eq19668 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19668
  have eq19681 : (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19680
  have eq19741 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq19679
       grind)
    | exact superpose eq19679 eq44
    | exact resolve eq44 eq19679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq19679
  have eq19774 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq19741
    | exact resolve eq19741 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19741
  have eq20266 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19681
       grind)
    | exact superpose eq19681 eq75
    | exact resolve eq75 eq19681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq19681
  have eq20916 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20266
       have i₂ := eq19658
       grind)
    | exact superpose eq19658 eq20266
    | exact resolve eq20266 eq19658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19658 eq20266
  have eq20970 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20916
  have eq20977 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20970
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20970
    | exact resolve eq20970 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20970
  have eq20994 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20977 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq20977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20977
  have eq21006 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20994
  have eq21012 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq21006
    | exact resolve eq21006 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21006
  have eq21013 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21012
  have eq21028 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21013 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq21013
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21013
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21013
       grind)
    | exact resolve eq13 eq21013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21013
  have eq21055 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21028
  have eq21066 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq21055
    | exact resolve eq21055 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21055
  have eq21566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21066 eq19774
    | exact resolve eq19774 eq21066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19774 eq21066
  have eq21576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq21566
  have eq21580 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq21576
       have r₂ := eq27
       grind)
    | exact resolve eq21576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21576
  have eq21594 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21580 eq581
    | exact resolve eq581 eq21580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581 eq21580
  have eq21788 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21594 eq4248
    | exact resolve eq4248 eq21594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4248 eq21594
  have eq21844 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq21788
    | exact resolve eq21788 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21788
  have eq21918 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq21844
       grind)
    | exact superpose eq21844 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq21844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21933 : y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq21918
  have eq28215 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq21933
       grind)
    | exact superpose eq21933 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq21933
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21933
       grind)
    | exact resolve eq13 eq21933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28241 : x ≠ y ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq21933
  have eq28242 : y = (k y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq28215
  have eq28397 : x = y ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq21844
       have i₂ := eq28242
       grind)
    | exact superpose eq28242 eq21844
    | exact resolve eq21844 eq28242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21844 eq28242
  have eq28426 : x = y ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq28397
  have eq28445 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq28426
       have r₂ := eq28241
       grind)
    | exact resolve eq28426 eq28241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28241 eq28426
  have eq28489 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq549 y y
       have i₂ := eq28445
       grind)
    | exact superpose eq28445 eq549
    | exact resolve eq549 eq28445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28445
  have eq28504 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28489
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28489
    | exact resolve eq28489 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28489
  have eq28505 : y = (M.op x y) := by grind
  clear eq28504
  have eq28520 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq28505 eq20
    | exact resolve eq20 eq28505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq28569 : x = (M.op y y) := by
    first
    | exact superpose eq28505 eq580
    | exact resolve eq580 eq28505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq28678 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28520
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28520
    | exact resolve eq28520 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28520
  have eq29245 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq28678 eq26
    | exact resolve eq26 eq28678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq29452 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq17716
       have i₂ := eq28569
       grind)
    | exact superpose eq28569 eq17716
    | exact resolve eq17716 eq28569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17716
  have eq29457 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq28569
       grind)
    | exact superpose eq28569 eq13
    | exact resolve eq13 eq28569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28569
  have eq29495 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq28678 eq29452
    | exact resolve eq29452 eq28678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29452
  have eq29503 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq29495
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29495
    | exact resolve eq29495 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29495
  have eq32301 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq29503 eq4469
    | exact resolve eq4469 eq29503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4469
  have eq32330 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq29503 eq549
    | exact resolve eq549 eq29503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq29503
  have eq32343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29245 eq32330
    | exact resolve eq32330 eq29245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32330
  have eq32358 : (τ (σ x)) = (k y y) ∨ x = y := by
    first
    | exact superpose eq28505 eq32301
    | exact resolve eq32301 eq28505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28505 eq32301
  have eq32359 : x = y := by
    first
    | (have r₁ := eq32343
       have r₂ := eq27
       grind)
    | exact resolve eq32343 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32343
  have eq32371 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq28 eq32358
    | exact resolve eq32358 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq32358
  have eq32378 : x = (k y y) := by
    first
    | (have r₁ := eq32371
       have r₂ := eq29457
       grind)
    | exact resolve eq32371 eq29457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29457 eq32371
  have eq32380 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq32359
       grind)
    | exact superpose eq32359 eq24
    | exact resolve eq24 eq32359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq32577 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28678 eq32380
    | exact resolve eq32380 eq28678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28678 eq32380
  have eq32660 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq32577
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32577
    | exact resolve eq32577 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32577
  have eq33508 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq32660 eq29245
    | exact resolve eq29245 eq32660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29245
  have eq33725 : x = (k x x) := by
    first
    | (have i₁ := eq32378
       have i₂ := eq32359
       grind)
    | exact superpose eq32359 eq32378
    | exact resolve eq32378 eq32359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32359 eq32378
  have eq33751 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11879 x x
       have i₂ := eq33725
       grind)
    | exact superpose eq33725 eq11879
    | (have j0 := eq11879 x x
       grind)
    | exact resolve eq11879 eq33725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11879 eq33725
  have eq33752 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq33751
  have eq33767 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq33752
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33752
    | exact resolve eq33752 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq33752
  have eq33786 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq32660 eq33767
    | exact resolve eq33767 eq32660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32660 eq33767
  have eq34086 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33786 eq33508
    | exact resolve eq33508 eq33786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33508 eq33786
  have eq34087 : False := by grind
  exact eq34087

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  clear eq35
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
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
  have eq56 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
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
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq73 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  clear eq43
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq73
  have eq89 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq92 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq103 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq89
       grind)
    | exact superpose eq89 eq16
    | exact resolve eq16 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq104
    | exact resolve eq104 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105
    | exact resolve eq105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq90
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq107
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
  have eq152 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq129 eq16
    | exact resolve eq16 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq221 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq274 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq62
    | (have j0 := eq62 y x
       grind)
    | exact resolve eq62 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq62
    | (have j0 := eq62 (σ y) (σ x)
       grind)
    | exact resolve eq62 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq59 (M.op X0 X0)
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq59
    | exact resolve eq59 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : y ≠ (M.op y y) ∨ (M.op x y) = (k (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq274 eq13
    | (have j0 := eq13 y y
       grind)
    | exact resolve eq13 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq446 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (M.op X0 X0) X0 X1 X2
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq455 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq58 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 y x X0 X1
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq459 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq462 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq58 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq483 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X2 (M.op X0 X1) X1
       have i₂ := eq62 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq62 eq58
    | exact resolve eq58 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq602 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq59 (σ X0)
       have i₂ := eq69 X0 X0
       grind)
    | exact superpose eq69 eq59
    | (have j1 := eq69 X0 X0
       grind)
    | exact resolve eq59 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq69 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq69 X0 X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq613 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq607 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607
  have eq615 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq602 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq620 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq613 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq613 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq613 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq613 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq626 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq620 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq620
    | (have j0 := eq620 X0 X1
       grind)
    | exact resolve eq620 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq2006 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq221 X0 sF4
       have i₂ := eq62 sF4 sF4
       grind)
    | exact superpose eq62 eq221
    | exact resolve eq221 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2954 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (M.op X0 (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq459
    | (have j0 := eq459 (σ y) X0 (σ x)
       grind)
    | exact resolve eq459 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2976 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq459 X0 X0 X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq459
    | exact resolve eq459 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq3003 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq2976 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2976
    | (have j0 := eq2976 y x
       grind)
    | exact resolve eq2976 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3182 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq464 x X1 X0
       have i₂ := eq62 x x
       grind)
    | exact superpose eq62 eq464
    | exact resolve eq464 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq3261 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3182 sF0 sF0
       have i₂ := eq59 sF0
       grind)
    | exact superpose eq59 eq3182
    | exact resolve eq3182 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3182
  have eq3364 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq615 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq615
    | (have j0 := eq615 X0
       have j1 := eq11 (σ X0) (σ X0)
       grind)
    | exact resolve eq615 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq3383 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3364 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3364
  have eq3428 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq455 (M.op y X0) X0
       have i₂ := eq62 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq62 eq455
    | exact resolve eq455 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455
  have eq3569 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq462 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq59 (M.op X0 X1)
       grind)
    | exact superpose eq59 eq462
    | exact resolve eq462 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq3909 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq92 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq92
    | (have j0 := eq92 y
       grind)
    | exact resolve eq92 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq3925 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq3909
  have eq3929 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3925
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq3925
    | exact resolve eq3925 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3925
  have eq7057 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq446 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq62 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq62 eq446
    | exact resolve eq446 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq12196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq12203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq12196
    | exact resolve eq12196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12196
  have eq12214 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq12203
       have r₂ := eq27
       grind)
    | exact resolve eq12203 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12203
  have eq12216 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq12214
    | exact resolve eq12214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12214
  have eq12223 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12216 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq12216
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12216
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq12216
       grind)
    | exact resolve eq13 eq12216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12216
  have eq12236 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq12223
  have eq12352 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq12236 eq55
    | exact resolve eq55 eq12236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq12236
  have eq12371 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq12352
    | exact resolve eq12352 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12352
  have eq12374 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq12371
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq12371
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq12371
       have r₂ := eq13 x y
       grind)
    | exact resolve eq12371 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12371
  have eq12376 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq12374
       grind)
    | exact superpose eq12374 eq44
    | exact resolve eq44 eq12374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq12383 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq12374
       grind)
    | exact superpose eq12374 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq12374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12374
  have eq12392 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12383
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12383
    | exact resolve eq12383 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12383
  have eq12393 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12392
  have eq12400 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12376
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12376
    | exact resolve eq12376 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12376
  have eq12544 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12400 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq12400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12400
  have eq12550 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12544
    | exact resolve eq12544 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12544
  have eq12551 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12550
  have eq13535 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2976 x y
       have i₂ := eq12393
       grind)
    | exact superpose eq12393 eq2976
    | exact resolve eq2976 eq12393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13536 : x ≠ y ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq13778 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12551 eq2976
    | exact resolve eq2976 eq12551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976 eq12551
  have eq20579 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13535
       have i₂ := eq12393
       grind)
    | exact superpose eq12393 eq13535
    | exact resolve eq13535 eq12393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12393
  have eq20586 : x ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq13535
       grind)
    | exact superpose eq13535 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq13535
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq13535
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq13535
       grind)
    | exact resolve eq12 eq13535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13535
  have eq20603 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq20579
  have eq20605 : x ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq20586
       have r₂ := eq12 x x
       grind)
    | (have r₁ := eq20586
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq20586
       have r₂ := eq12 y x
       grind)
    | exact resolve eq20586 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20586
  have eq20606 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq20603
       have r₂ := eq13536
       grind)
    | exact resolve eq20603 eq13536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13536 eq20603
  have eq20607 : y = (M.op x y) ∨ x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq20605
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20605
    | exact resolve eq20605 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20605
  have eq20608 : x ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq20607
  have eq20622 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq20606
       grind)
    | exact superpose eq20606 eq59
    | exact resolve eq59 eq20606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq20606
  have eq20650 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20622
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20622
    | exact resolve eq20622 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20622
  have eq20662 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq20650
       grind)
    | exact superpose eq20650 eq14
    | exact resolve eq14 eq20650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22200 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq13778
  have eq26107 : y = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20662 y
       have i₂ := eq20650
       grind)
    | exact superpose eq20650 eq20662
    | exact resolve eq20662 eq20650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20662
  have eq26147 : y = (M.op x (M.op y y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq26107
  have eq29860 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3569 x x y
       have i₂ := eq20650
       grind)
    | exact superpose eq20650 eq3569
    | exact resolve eq3569 eq20650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30014 : ∀ X0 : G, (M.op x x) = (M.op (M.op x X0) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3569 x X0 x
       have i₂ := eq29860 x
       grind)
    | exact superpose eq29860 eq3569
    | exact resolve eq3569 eq29860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29860
  have eq30265 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30014 (M.op y y)
       have i₂ := eq26147
       grind)
    | exact superpose eq26147 eq30014
    | exact resolve eq30014 eq26147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26147 eq30014
  have eq30316 : (M.op x x) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30265
  have eq30325 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20650
       have i₂ := eq30316
       grind)
    | exact superpose eq30316 eq20650
    | exact resolve eq20650 eq30316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20650 eq30316
  have eq30362 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30325
  have eq30378 : x ≠ x ∨ y = (M.op x y) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20608
       have i₂ := eq30362
       grind)
    | exact superpose eq30362 eq20608
    | (have r₁ := eq20608
       have r₂ := eq30362
       grind)
    | exact resolve eq20608 eq30362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20608 eq30362
  have eq30443 : x ≠ x ∨ y = (M.op x y) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30378
  have eq30444 : y = (M.op x y) ∨ x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq30443
  have eq30461 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30444
       have r₂ := eq50
       grind)
    | exact resolve eq30444 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq30444
  have eq30468 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq30461
       grind)
    | exact superpose eq30461 eq89
    | exact resolve eq89 eq30461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq30461
  have eq30502 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30468
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30468
    | exact resolve eq30468 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30468
  have eq30509 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq30502
       have r₂ := eq51
       grind)
    | exact resolve eq30502 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq30502
  have eq30534 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30509 eq103
    | exact resolve eq103 eq30509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq30545 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30509 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq30509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30509
  have eq30551 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq30545
    | exact resolve eq30545 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30545
  have eq30558 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq30534
    | exact resolve eq30534 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq30534
  have eq30562 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq30551
    | exact resolve eq30551 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30551
  have eq30578 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq30558
       grind)
    | exact superpose eq30558 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq30558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30589 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30578
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30578
    | exact resolve eq30578 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30578
  have eq30590 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq30589
  have eq30605 : x = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30590
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30590
    | exact resolve eq30590 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30590
  have eq30634 : x ≠ x ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq30605
       grind)
    | exact superpose eq30605 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq30605
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq30605
       grind)
    | exact resolve eq12 eq30605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30636 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq30605
       grind)
    | exact superpose eq30605 eq14
    | exact resolve eq14 eq30605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30655 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq30634
  have eq30662 : y = (M.op x y) ∨ (k y x) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30655
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30655
    | exact resolve eq30655 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30655
  have eq30663 : (k y x) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq30662
  have eq31269 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30558
       have i₂ := eq30663
       grind)
    | exact superpose eq30663 eq30558
    | exact resolve eq30558 eq30663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30558 eq30663
  have eq31277 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq31269
  have eq31359 : x ≠ x ∨ x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq31277
       grind)
    | exact superpose eq31277 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq31277
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq31277
       grind)
    | exact resolve eq13 eq31277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31277
  have eq31379 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq31359
  have eq31441 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq626 x x
       have i₂ := eq31379
       grind)
    | exact superpose eq31379 eq626
    | (have j0 := eq626 x x
       grind)
    | exact resolve eq626 eq31379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31379
  have eq31442 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq31441
  have eq31443 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq31442
  have eq31459 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq31443
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31443
    | exact resolve eq31443 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31443
  have eq31539 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31459 eq22200
    | (have r₁ := eq22200
       have r₂ := eq31459
       grind)
    | exact resolve eq22200 eq31459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22200
  have eq31550 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31459 eq2006
    | exact resolve eq2006 eq31459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006 eq31459
  have eq31603 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq31539
  have eq31604 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq31603
  have eq32040 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31550 eq62
    | exact resolve eq62 eq31550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31550
  have eq38896 : y = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30636 y
       have i₂ := eq30605
       grind)
    | exact superpose eq30605 eq30636
    | exact resolve eq30636 eq30605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30636
  have eq38951 : y = (M.op x (M.op y y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq38896
  have eq38995 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq483 x (M.op y y) x
       have i₂ := eq38951
       grind)
    | exact superpose eq38951 eq483
    | exact resolve eq483 eq38951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483 eq38951
  have eq45345 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq38995 y
       have i₂ := eq30605
       grind)
    | exact superpose eq30605 eq38995
    | exact resolve eq38995 eq30605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30605 eq38995
  have eq45405 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq45345
  have eq45425 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45405
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45405
    | exact resolve eq45405 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45405
  have eq45770 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq45425
       grind)
    | exact superpose eq45425 eq113
    | exact resolve eq113 eq45425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq45425
  have eq45852 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq45770
  have eq45862 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq45852
    | exact resolve eq45852 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45852
  have eq47458 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq3929 eq45862
    | exact resolve eq45862 eq3929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3929
  have eq66998 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32040 eq3569
    | exact resolve eq3569 eq32040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32040
  have eq78843 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2954 eq66998
    | exact resolve eq66998 eq2954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2954 eq66998
  have eq138003 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq47458 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq47458
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq47458
       grind)
    | exact resolve eq13 eq47458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138027 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq47458
  have eq138028 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq138003
  have eq142807 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq138028 eq45862
    | exact resolve eq45862 eq138028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45862 eq138028
  have eq142844 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq142807
  have eq142855 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq142844
       have r₂ := eq138027
       grind)
    | exact resolve eq142844 eq138027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138027 eq142844
  have eq142893 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq142855 eq78843
    | exact resolve eq78843 eq142855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78843
  have eq142900 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq142855 eq278
    | exact resolve eq278 eq142855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq142911 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq142855 eq62
    | exact resolve eq62 eq142855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142926 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq142855 eq3569
    | exact resolve eq3569 eq142855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142855
  have eq142932 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq142893
  have eq155200 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq142911 eq142926
    | exact resolve eq142926 eq142911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142911 eq142926
  have eq155258 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq155200 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155200
  have eq155308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31604 eq155258
    | exact resolve eq155258 eq31604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31604 eq155258
  have eq155406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq155308
  have eq155431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq155406
    | exact resolve eq155406 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155406
  have eq155440 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq155431
       have r₂ := eq27
       grind)
    | exact resolve eq155431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155431
  have eq155492 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq155440 eq142932
    | exact resolve eq142932 eq155440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142932 eq155440
  have eq155509 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq155492
  have eq155542 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq155509
    | exact resolve eq155509 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155509
  have eq155639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq155542 eq142900
    | exact resolve eq142900 eq155542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142900 eq155542
  have eq155686 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq155639
  have eq155696 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq155686
       have r₂ := eq27
       grind)
    | exact resolve eq155686 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155686
  have eq155699 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq155696 eq20
    | exact resolve eq20 eq155696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155844 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq155696 eq3261
    | exact resolve eq3261 eq155696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq155879 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq156015 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq155699
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq155699
    | exact resolve eq155699 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155699
  have eq156332 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq156015 eq26
    | exact resolve eq26 eq156015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156354 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq156015 eq275
    | exact resolve eq275 eq156015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq157652 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3428 x
       have i₂ := eq155844
       grind)
    | exact superpose eq155844 eq3428
    | exact resolve eq3428 eq155844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428 eq155844
  have eq157729 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq157652
       have i₂ := eq62 x x
       grind)
    | exact superpose eq62 eq157652
    | exact resolve eq157652 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157652
  have eq159680 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq157729 eq14
    | exact resolve eq14 eq157729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157729
  have eq177687 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq159680 eq7057
    | exact resolve eq7057 eq159680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7057 eq159680
  have eq177767 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq155696 eq177687
    | exact resolve eq177687 eq155696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177687
  have eq177894 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq177767
       have r₂ := eq155879
       grind)
    | exact resolve eq177767 eq155879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155879 eq177767
  have eq177896 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq177894
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177894
    | exact resolve eq177894 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177894
  have eq177900 : y ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq288
       have i₂ := eq177896
       grind)
    | exact superpose eq177896 eq288
    | exact resolve eq288 eq177896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177958 : y ≠ (M.op x y) ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq177896
       grind)
    | exact superpose eq177896 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq177896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177896
  have eq178017 : y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq177958
       have r₂ := eq155696
       grind)
    | exact resolve eq177958 eq155696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177958
  have eq178026 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq177900
       have r₂ := eq155696
       grind)
    | exact resolve eq177900 eq155696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155696 eq177900
  have eq178980 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq626 y y
       have i₂ := eq178017
       grind)
    | exact superpose eq178017 eq626
    | (have j0 := eq626 y y
       grind)
    | exact resolve eq626 eq178017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178017
  have eq178983 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq178980
  have eq178984 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq178983
  have eq179015 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq178984
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq178984
    | exact resolve eq178984 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178984
  have eq179804 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq178026 eq626
    | (have j0 := eq626 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq626 eq178026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178026
  have eq179807 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq179804
  have eq179808 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq179807
  have eq179853 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq179808
    | exact resolve eq179808 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179808
  have eq182897 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq179015 eq3569
    | exact resolve eq3569 eq179015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3569
  have eq185694 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179853 eq156354
    | exact resolve eq156354 eq179853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156354 eq179853
  have eq185761 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq185694
  have eq302384 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq179015 eq182897
    | exact resolve eq182897 eq179015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179015 eq182897
  have eq302506 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq302384 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302384
  have eq302565 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30562 eq302506
    | exact resolve eq302506 eq30562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30562 eq302506
  have eq302711 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq302565
  have eq302733 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq302711
    | exact resolve eq302711 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302711
  have eq302734 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq302733
  have eq302739 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq302734 eq27
    | exact resolve eq27 eq302734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302734
  have eq302946 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq302739
       have r₂ := eq156015
       grind)
    | exact resolve eq302739 eq156015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156015 eq302739
  have eq303062 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq302946 eq185761
    | exact resolve eq185761 eq302946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185761 eq302946
  have eq303115 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq303062
  have eq303967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq303115 eq156332
    | exact resolve eq156332 eq303115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156332 eq303115
  have eq304047 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq303967
  have eq304051 : x = (M.op x y) := by
    first
    | (have r₁ := eq304047
       have r₂ := eq27
       grind)
    | exact resolve eq304047 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304047
  have eq304055 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq304051 eq20
    | exact resolve eq20 eq304051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq304216 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq304051 eq3003
    | exact resolve eq3003 eq304051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3003
  have eq304274 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq304216
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq304216
    | exact resolve eq304216 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq304216
  have eq304418 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq304055
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq304055
    | exact resolve eq304055 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304055
  have eq304419 : x = (M.op y y) := by
    first
    | exact superpose eq304051 eq304274
    | exact resolve eq304274 eq304051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304274
  have eq304422 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq304418 eq26
    | exact resolve eq26 eq304418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq304989 : x ≠ y ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | (have i₁ := eq288
       have i₂ := eq304419
       grind)
    | exact superpose eq304419 eq288
    | exact resolve eq288 eq304419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq305091 : y = (M.op x x) := by
    first
    | (have i₁ := eq62 y y
       have i₂ := eq304419
       grind)
    | exact superpose eq304419 eq62
    | exact resolve eq62 eq304419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq304419
  have eq305147 : x ≠ y ∨ x = (k x x) := by
    first
    | exact superpose eq304051 eq304989
    | exact resolve eq304989 eq304051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304989
  have eq305627 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq305091
       grind)
    | exact superpose eq305091 eq78
    | exact resolve eq78 eq305091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq305732 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq3383 x
       have i₂ := eq305091
       grind)
    | exact superpose eq305091 eq3383
    | (have j0 := eq3383 x
       grind)
    | exact resolve eq3383 eq305091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3383 eq305091
  have eq305793 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq305732
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq305732
    | exact resolve eq305732 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305732
  have eq305808 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq304418 eq305627
    | exact resolve eq305627 eq304418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305627
  have eq305815 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq305793
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq305793
    | exact resolve eq305793 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305793
  have eq305821 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq305808
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq305808
    | exact resolve eq305808 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305808
  have eq305824 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq26 eq305815
    | exact resolve eq305815 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq305815
  have eq305828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq304418 eq305824
    | exact resolve eq305824 eq304418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305824
  have eq305833 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq305828
       have r₂ := eq27
       grind)
    | exact resolve eq305828 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305828
  have eq305835 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq305833
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq305833
    | exact resolve eq305833 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305833
  have eq305836 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq304418 eq305835
    | exact resolve eq305835 eq304418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305835
  have eq310743 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq305821 eq152
    | exact resolve eq152 eq305821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305821
  have eq310803 : (τ (σ y)) = (k x x) ∨ x = y := by
    first
    | exact superpose eq304051 eq310743
    | exact resolve eq310743 eq304051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310743
  have eq310814 : y = (k x x) ∨ x = y := by
    first
    | exact superpose eq29 eq310803
    | exact resolve eq310803 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq310803
  have eq310871 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq305836 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq305836
       grind)
    | exact resolve eq13 eq305836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305836
  have eq310910 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq310871
  have eq311435 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq310910 eq152
    | exact resolve eq152 eq310910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq310910
  have eq311516 : (τ (σ (M.op x y))) = (k x x) ∨ x = y := by
    first
    | exact superpose eq304051 eq311435
    | exact resolve eq311435 eq304051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311435
  have eq311527 : (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq30 eq311516
    | exact resolve eq311516 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq311516
  have eq311538 : x = (k x x) ∨ x = y := by
    first
    | exact superpose eq304051 eq311527
    | exact resolve eq311527 eq304051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304051 eq311527
  have eq311544 : x = (k x x) := by
    first
    | (have r₁ := eq311538
       have r₂ := eq305147
       grind)
    | exact resolve eq311538 eq305147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305147 eq311538
  have eq311570 : x = y ∨ x = y := by
    first
    | (have i₁ := eq310814
       have i₂ := eq311544
       grind)
    | exact superpose eq311544 eq310814
    | exact resolve eq310814 eq311544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310814
  have eq311599 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq626 x x
       have i₂ := eq311544
       grind)
    | exact superpose eq311544 eq626
    | (have j0 := eq626 x x
       grind)
    | exact resolve eq626 eq311544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626 eq311544
  have eq311602 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq311599
  have eq311603 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq311602
  have eq311622 : x = y := by grind
  clear eq311570
  have eq311628 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq311603
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq311603
    | exact resolve eq311603 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311603
  have eq311672 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq304418 eq311628
    | exact resolve eq311628 eq304418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311628
  have eq311758 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq311622
       grind)
    | exact superpose eq311622 eq24
    | exact resolve eq24 eq311622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq311622
  have eq312537 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq311758
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq311758
    | exact resolve eq311758 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq311758
  have eq312695 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq304418 eq312537
    | exact resolve eq312537 eq304418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304418 eq312537
  have eq313526 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq312695 eq304422
    | exact resolve eq304422 eq312695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304422 eq312695
  have eq316714 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq311672 eq313526
    | exact resolve eq313526 eq311672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311672 eq313526
  have eq316715 : False := by grind
  exact eq316715

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxx_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  clear eq44
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
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
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : y ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq72 sF2
       grind)
    | exact superpose eq72 eq50
    | exact resolve eq50 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq72 x
       grind)
    | exact superpose eq72 eq76
    | exact resolve eq76 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq95 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq99 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq100 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq104 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq72 sF3
       grind)
    | exact superpose eq72 eq100
    | exact resolve eq100 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq72 y
       grind)
    | exact superpose eq72 eq104
    | exact resolve eq104 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq99
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq108
    | exact resolve eq108 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq114
    | exact resolve eq114 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq115
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq115
    | exact resolve eq115 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq128 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq125
       have i₂ := eq72 sF1
       grind)
    | exact superpose eq72 eq125
    | exact resolve eq125 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq72 sF0
       grind)
    | exact superpose eq72 eq128
    | exact resolve eq128 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq128
  have eq144 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq130 eq16
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq277 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1007 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq86 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1096
    | exact resolve eq1096 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1096
  have eq1100 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1097
       have r₂ := eq28
       grind)
    | exact resolve eq1097 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1097
  have eq1102 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1100
    | exact resolve eq1100 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq1105 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1102 eq68
    | (have r₁ := eq68
       have r₂ := eq1102
       grind)
    | exact resolve eq68 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1107 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq1102 eq52
    | exact resolve eq52 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1109 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1105
  have eq1163 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1109 eq116
    | exact resolve eq116 eq1109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1109
  have eq1167 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1163
  have eq1263 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1167 eq56
    | exact resolve eq56 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1467 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op X0 (M.op (σ (M.op x y)) X1)) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq1263 eq14
    | exact resolve eq14 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1478 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1263 eq14
    | exact resolve eq14 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq2442 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq1478
    | (have j0 := eq1478 (σ x)
       grind)
    | exact resolve eq1478 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1478
  have eq3489 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1107
    | (have j0 := eq1107 (σ x)
       grind)
    | exact resolve eq1107 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1107
  have eq3579 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1102 eq3489
    | exact resolve eq3489 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq3489
  have eq3589 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq3579
  have eq3604 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3589 eq14
    | exact resolve eq14 eq3589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589
  have eq3895 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq637 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq637
    | exact resolve eq637 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq5227 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1007 x y
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq1007
    | (have j0 := eq1007 x y
       grind)
    | exact resolve eq1007 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq5240 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5227
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5227
    | exact resolve eq5227 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5227
  have eq5271 : (σ x) = (σ y) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5240
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5240
    | exact resolve eq5240 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5240
  have eq5302 : (σ x) = (σ y) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5271
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5271
    | exact resolve eq5271 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq5332 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5302
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq5302
    | exact resolve eq5302 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5302
  have eq5362 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5332
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq5332
    | exact resolve eq5332 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5332
  have eq5385 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq5362
    | exact resolve eq5362 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5362
  have eq23478 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3604 eq277
    | exact resolve eq277 eq3604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq3604
  have eq24054 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2442 eq23478
    | exact resolve eq23478 eq2442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442 eq23478
  have eq24093 : (M.op (σ x) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq24054
  have eq24134 : (σ x) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24093 eq54
    | exact resolve eq54 eq24093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq24093
  have eq24191 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq24134 eq1467
    | exact resolve eq1467 eq24134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467 eq24134
  have eq24211 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq24191
  have eq24212 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq24211
    | exact resolve eq24211 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24211
  have eq24213 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq24212
       have r₂ := eq28
       grind)
    | exact resolve eq24212 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24212
  have eq24215 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq24213 eq30
    | exact resolve eq30 eq24213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq24213
  have eq24256 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq24215
    | exact resolve eq24215 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24215
  have eq24257 : y = (M.op x y) ∨ x = y := by grind
  clear eq24256
  have eq24261 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq24257 eq21
    | exact resolve eq21 eq24257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24263 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq24257 eq51
    | exact resolve eq51 eq24257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq24265 : y ≠ y ∨ (M.op y y) = (k y x) ∨ x = y := by
    first
    | exact superpose eq24257 eq67
    | (have r₁ := eq67
       have r₂ := eq24257
       grind)
    | exact resolve eq67 eq24257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq24268 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq24257 eq118
    | exact resolve eq118 eq24257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq24327 : (M.op y y) = (k y x) ∨ x = y := by grind
  clear eq24265
  have eq24373 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24268 X0
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq24268
    | exact resolve eq24268 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq24268
  have eq24378 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24261
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq24261
    | exact resolve eq24261 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24261
  have eq24411 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq24378 eq144
    | exact resolve eq144 eq24378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq24467 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq24378 eq5385
    | exact resolve eq5385 eq24378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5385 eq24378
  have eq24787 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq24467
       have r₂ := eq28
       grind)
    | exact resolve eq24467 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24467
  have eq24811 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq178 eq24411
    | exact resolve eq24411 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq24411
  have eq24870 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq24327
       grind)
    | exact superpose eq24327 eq99
    | exact resolve eq99 eq24327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq24327
  have eq24906 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq24870
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq24870
    | exact resolve eq24870 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24870
  have eq25926 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq24906 eq24373
    | exact resolve eq24373 eq24906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24373 eq24906
  have eq25932 : (M.op (σ y) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y := by grind
  clear eq25926
  have eq29790 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq25932 eq24787
    | exact resolve eq24787 eq25932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24787 eq25932
  have eq29793 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq29790
  have eq31237 : x = (M.op (M.op x y) (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq24263 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq24263
    | (have j0 := eq24263 x
       grind)
    | exact resolve eq24263 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24263
  have eq51317 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x y) X0) (M.op (M.op y y) (M.op y y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq24811 eq3895
    | exact resolve eq3895 eq24811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3895 eq24811
  have eq51456 : ∀ X0 : G, (M.op y y) = (M.op (M.op (M.op x y) X0) y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq51317 X0
       have i₂ := eq56 y y
       grind)
    | exact superpose eq56 eq51317
    | exact resolve eq51317 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq51317
  have eq51856 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq31237 eq51456
    | exact resolve eq51456 eq31237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31237 eq51456
  have eq51949 : (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq51856
  have eq51954 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq51949
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq51949
    | exact resolve eq51949 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51949
  have eq51957 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq106
       have i₂ := eq51954
       grind)
    | exact superpose eq51954 eq106
    | exact resolve eq106 eq51954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq51954
  have eq52109 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq51957
    | exact resolve eq51957 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51957
  have eq52779 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq52109 eq29793
    | (have r₁ := eq29793
       have r₂ := eq52109
       grind)
    | exact resolve eq29793 eq52109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29793 eq52109
  have eq52871 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq52779
  have eq52872 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq52871
  have eq52957 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq52872 eq29
    | exact resolve eq29 eq52872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52872
  have eq53168 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq52957
    | exact resolve eq52957 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq52957
  have eq53295 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq53168 eq24257
    | exact resolve eq24257 eq53168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24257 eq53168
  have eq53434 : x = y := by grind
  clear eq53295
  have eq53585 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq19
    | exact resolve eq19 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq53586 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq53434
       grind)
    | exact superpose eq53434 eq25
    | exact resolve eq25 eq53434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq53434
  have eq53713 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq53586
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq53586
    | exact resolve eq53586 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq53586
  have eq53750 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq53713 eq27
    | exact resolve eq27 eq53713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq53713
  have eq54038 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq53750 eq77
    | exact resolve eq77 eq53750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq53750
  have eq54115 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq54038
       have i₂ := eq53585
       grind)
    | exact superpose eq53585 eq54038
    | exact resolve eq54038 eq53585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53585 eq54038
  have eq54140 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54115 eq15
    | exact resolve eq15 eq54115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54115
  have eq54225 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq54140
    | exact resolve eq54140 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq54140
  have eq54246 : False := by grind
  exact eq54246

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxy_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq21 (M.op X0 X0)
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq21
    | exact resolve eq21 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 X0) X0
       have i₂ := eq21 X0
       grind)
    | exact superpose eq21 eq12
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq21 X0
       grind)
    | exact resolve eq12 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq34 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq35
    | exact resolve eq35 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35
  have eq37 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq23 X0 X0
       grind)
    | exact superpose eq23 eq36
    | exact resolve eq36 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq41 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq53 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq37 (τ X0)
       grind)
    | exact superpose eq37 eq18
    | exact resolve eq18 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq57 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq58 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53
    | exact resolve eq53 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq83 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57
    | exact resolve eq57 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq173 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq58 (τ X0)
       grind)
    | exact superpose eq58 eq18
    | exact resolve eq18 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq174 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq173 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq173
    | exact resolve eq173 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq204 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq41
    | exact resolve eq41 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq41 X0 X0
       grind)
    | exact superpose eq41 eq23
    | (have j1 := eq41 X0 X0
       grind)
    | exact resolve eq23 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq228 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq217 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq264 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq31 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq20 X1 X1 X0 X2
       grind)
    | exact superpose eq20 eq31
    | exact resolve eq31 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq31
  have eq357 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq264 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq21 (M.op X0 X1)
       grind)
    | exact superpose eq21 eq264
    | exact resolve eq264 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq536 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))
       have i₂ := eq174 (τ X0)
       grind)
    | exact superpose eq174 eq18
    | exact resolve eq18 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq174
  have eq539 : ∀ X0 : G, (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) = X0 := by
    intro X0
    first
    | (have i₁ := eq536 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq536
    | exact resolve eq536 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq15396 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 (σ (τ X0))) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq228 (τ X0) X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq228
    | (have j0 := eq228 (τ X0) X1
       grind)
    | exact resolve eq228 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq15526 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15396 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15396
    | (have j0 := eq15396 X0 X1
       grind)
    | exact resolve eq15396 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15396
  have eq15550 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15526 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15526
    | (have j0 := eq15526 X0 X1
       grind)
    | exact resolve eq15526 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15526
  have eq15624 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq357 (k X0 X0) X0
       have i₂ := eq15550 X0 (k X0 X0)
       grind)
    | exact superpose eq15550 eq357
    | (have j1 := eq15550 X0 x
       grind)
    | exact resolve eq357 eq15550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq15550
  have eq15849 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 (k X0 X0) (k X0 X0)
       have i₂ := eq15624 X0
       grind)
    | exact superpose eq15624 eq23
    | (have j1 := eq15624 X0
       grind)
    | exact resolve eq23 eq15624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15624
  have eq15944 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15849 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq15849 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq15849 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15849
  have eq16248 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq15944 (σ X0)
       grind)
    | exact superpose eq15944 eq15
    | exact resolve eq15 eq15944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16254 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq83 X0 X0
       have i₂ := eq15944 (τ X0)
       grind)
    | exact superpose eq15944 eq83
    | exact resolve eq83 eq15944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq16278 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16254 X0
       have i₂ := eq15944 X0
       grind)
    | exact superpose eq15944 eq16254
    | exact resolve eq16254 eq15944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16254
  have eq16284 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16248 X0
       have i₂ := eq15944 X0
       grind)
    | exact superpose eq15944 eq16248
    | exact resolve eq16248 eq15944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15944 eq16248
  have eq16862 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq21 (σ X0)
       have i₂ := eq16284 X0
       grind)
    | exact superpose eq16284 eq21
    | exact resolve eq21 eq16284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43123 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0))))))))))) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) ∨ (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))) X1
       have i₂ := eq539 (τ X0)
       grind)
    | exact superpose eq539 eq204
    | (have j0 := eq204 X0 (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))) X1
       grind)
    | exact resolve eq204 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq43163 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) (k X0 (σ (σ (σ (σ (τ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))))))) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) ∨ (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43123 X0 X1
       have i₂ := eq16278 (τ (τ (τ X0)))
       grind)
    | exact superpose eq16278 eq43123
    | (have j0 := eq43123 X0 X1
       grind)
    | exact resolve eq43123 eq16278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43123
  have eq43217 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))))))) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) ∨ (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43163 X0 X1
       have i₂ := eq11 (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))
       grind)
    | exact superpose eq11 eq43163
    | (have j0 := eq43163 X0 X1
       grind)
    | exact resolve eq43163 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43163
  have eq43265 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) ∨ (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43217 X0 X1
       have i₂ := eq539 X0
       grind)
    | exact superpose eq539 eq43217
    | (have j0 := eq43217 X0 X1
       grind)
    | exact resolve eq43217 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43217
  have eq43306 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) ∨ (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43265 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq43265
    | (have j0 := eq43265 X0 X1
       grind)
    | exact resolve eq43265 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43265
  have eq43338 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (σ (τ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))))) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43306 X0 X1
       have i₂ := eq16278 (τ (τ (τ X0)))
       grind)
    | exact superpose eq16278 eq43306
    | (have j0 := eq43306 X0 X1
       grind)
    | exact resolve eq43306 eq16278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43306
  have eq43370 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43338 X0 X1
       have i₂ := eq11 (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))
       grind)
    | exact superpose eq11 eq43338
    | (have j0 := eq43338 X0 X1
       grind)
    | exact resolve eq43338 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43338
  have eq43396 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43370 X0 X1
       have i₂ := eq539 X0
       grind)
    | exact superpose eq539 eq43370
    | (have j0 := eq43370 X0 X1
       grind)
    | exact resolve eq43370 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43370
  have eq43410 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) = (M.op (k X0 (σ (σ (σ (σ (M.op (τ (τ (τ (τ X0)))) (τ (τ (τ (τ X0)))))))))) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43396 X0 X1
       have i₂ := eq16284 X1
       grind)
    | exact superpose eq16284 eq43396
    | (have j0 := eq43396 X0 X1
       grind)
    | exact resolve eq43396 eq16284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16284 eq43396
  have eq43414 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (σ (τ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))))) = (M.op (k X0 (σ (σ (σ (σ (τ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))))) (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43410 X0 X1
       have i₂ := eq16278 (τ (τ (τ X0)))
       grind)
    | exact superpose eq16278 eq43410
    | (have j0 := eq43410 X0 X1
       grind)
    | exact resolve eq43410 eq16278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43410
  have eq43416 : ∀ X0 X1 : G, (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) = (M.op (k X0 (σ (σ (σ (M.op (τ (τ (τ X0))) (τ (τ (τ X0)))))))) (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43414 X0 X1
       have i₂ := eq11 (M.op (τ (τ (τ X0))) (τ (τ (τ X0))))
       grind)
    | exact superpose eq11 eq43414
    | (have j0 := eq43414 X0 X1
       grind)
    | exact resolve eq43414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43414
  have eq43418 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq43416 X0 X1
       have i₂ := eq539 X0
       grind)
    | exact superpose eq539 eq43416
    | (have j0 := eq43416 X0 X1
       grind)
    | exact resolve eq43416 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq43416
  have eq43419 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq43418 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq43418 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | (have r₁ := eq43418 (M.op (σ (M.op X1 X1)) X0) X1
       have r₂ := eq12 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq43418 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43418
  have eq44553 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq43419 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43419
    | (have j0 := eq43419 X1 (τ X0)
       grind)
    | exact resolve eq43419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44594 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq43419 (σ X1) X0
       grind)
    | exact superpose eq43419 eq15
    | (have j1 := eq43419 (σ X1) X0
       grind)
    | exact resolve eq15 eq43419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43419
  have eq44729 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44553 X0 X1
       have i₂ := eq16278 X0
       grind)
    | exact superpose eq16278 eq44553
    | (have j0 := eq44553 X0 X1
       grind)
    | exact resolve eq44553 eq16278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16278 eq44553
  have eq44763 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44729 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq44729
    | (have j0 := eq44729 X0 X1
       grind)
    | exact resolve eq44729 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44729
  have eq44848 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq44763 X0 (τ X1)
       grind)
    | exact superpose eq44763 eq19
    | (have j1 := eq44763 X0 (τ X1)
       grind)
    | exact resolve eq19 eq44763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq44763
  have eq50988 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44848 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44848
    | exact resolve eq44848 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44848
  have eq51191 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq50988 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq50988
    | (have j0 := eq50988 X0 X1
       grind)
    | exact resolve eq50988 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50988
  have eq237150 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44594 x y
       grind)
    | exact superpose eq44594 eq16
    | (have j1 := eq44594 x y
       grind)
    | exact resolve eq16 eq44594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44594
  have eq239342 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq237150
       have i₂ := eq51191 y x
       grind)
    | exact superpose eq51191 eq237150
    | (have j1 := eq51191 y x
       grind)
    | (have r₁ := eq237150
       have r₂ := eq51191 y x
       grind)
    | exact resolve eq237150 eq51191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51191 eq237150
  have eq239345 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq239342
  have eq239385 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq239345
       grind)
    | exact superpose eq239345 eq10
    | exact resolve eq10 eq239345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239345
  have eq239731 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq239385
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq239385
    | exact resolve eq239385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239385
  have eq239732 : y = (M.op x x) := by grind
  clear eq239731
  have eq241204 : x = (M.op x y) := by
    first
    | (have i₁ := eq21 x
       have i₂ := eq239732
       grind)
    | exact superpose eq239732 eq21
    | exact resolve eq21 eq239732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq241256 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16862 x
       have i₂ := eq239732
       grind)
    | exact superpose eq239732 eq16862
    | exact resolve eq16862 eq239732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16862 eq239732
  have eq253101 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq241256
       grind)
    | exact superpose eq241256 eq16
    | exact resolve eq16 eq241256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241256
  have eq253463 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq253101
       have i₂ := eq241204
       grind)
    | exact superpose eq241204 eq253101
    | exact resolve eq253101 eq241204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241204 eq253101
  have eq253464 : False := by grind
  exact eq253464

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxx_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
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
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq78
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq108
    | exact resolve eq108 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq191 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq249 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq54
    | exact resolve eq54 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq466 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3448 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq463 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq463
    | exact resolve eq463 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq4133 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq466 X0 X0 X2 X3 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq466
    | exact resolve eq466 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq4533 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq191 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq191
    | (have j0 := eq191 y
       grind)
    | exact resolve eq191 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq191
  have eq4548 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4533
  have eq4551 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq4548
       have i₂ := eq78
       grind)
    | exact superpose eq78 eq4548
    | exact resolve eq4548 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4548
  have eq4574 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq4551
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq4551 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4551
  have eq4603 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq4574 eq89
    | exact resolve eq89 eq4574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq14551 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4574 eq105
    | exact resolve eq105 eq4574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq20280 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4133 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq4133
    | exact resolve eq4133 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq4133
  have eq21714 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq14551
       grind)
    | exact superpose eq14551 eq16
    | exact resolve eq16 eq14551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14551
  have eq21780 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4603 eq21714
    | exact resolve eq21714 eq4603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21714
  have eq21786 : (M.op y y) = (k y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq21780
       have r₂ := eq13 y y
       grind)
    | exact resolve eq21780 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21780
  have eq21787 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq21786
       grind)
    | exact superpose eq21786 eq78
    | exact resolve eq78 eq21786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq21825 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq4574 eq21787
    | exact resolve eq21787 eq4574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4574 eq21787
  have eq32992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq32993 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq32992
    | exact resolve eq32992 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32992
  have eq33004 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq32993
       have r₂ := eq28
       grind)
    | exact resolve eq32993 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32993
  have eq33041 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq33004 eq3448
    | exact resolve eq3448 eq33004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35538 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq33041 eq33004
    | exact resolve eq33004 eq33041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33004 eq33041
  have eq35583 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq35538
  have eq35623 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq35583 eq56
    | exact resolve eq56 eq35583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35583
  have eq35645 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq35623
  have eq35681 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq35645 eq4603
    | exact resolve eq4603 eq35645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4603 eq35645
  have eq35770 : (τ (σ x)) = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq35681
       have i₂ := eq21786
       grind)
    | exact superpose eq21786 eq35681
    | exact resolve eq35681 eq21786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21786 eq35681
  have eq35779 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq35770
    | exact resolve eq35770 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35770
  have eq35780 : y = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq35779
  have eq35818 : (M.op x x) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3448 x y
       have i₂ := eq35780
       grind)
    | exact superpose eq35780 eq3448
    | exact resolve eq3448 eq35780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3448
  have eq37187 : y = (M.op x x) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq35780
       have i₂ := eq35818
       grind)
    | exact superpose eq35818 eq35780
    | exact resolve eq35780 eq35818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35780 eq35818
  have eq37234 : y = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq37187
  have eq37276 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq37234
       grind)
    | exact superpose eq37234 eq56
    | exact resolve eq56 eq37234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq37234
  have eq37300 : x = (M.op y y) := by grind
  clear eq37276
  have eq37338 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21825
       have i₂ := eq37300
       grind)
    | exact superpose eq37300 eq21825
    | exact resolve eq21825 eq37300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21825
  have eq37395 : x = (M.op x y) := by
    first
    | (have i₁ := eq20280 y y
       have i₂ := eq37300
       grind)
    | exact superpose eq37300 eq20280
    | exact resolve eq20280 eq37300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20280 eq37300
  have eq37399 : x = (M.op x y) := by
    first
    | (have i₁ := eq37395
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37395
    | exact resolve eq37395 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq37395
  have eq37422 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq37338
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37338
    | exact resolve eq37338 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37338
  have eq37433 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq37399 eq21
    | exact resolve eq21 eq37399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq37399
  have eq37669 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq37433
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq37433
    | exact resolve eq37433 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq37433
  have eq37738 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq37669 eq27
    | exact resolve eq27 eq37669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq39001 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq37669 eq37422
    | exact resolve eq37422 eq37669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37422 eq37669
  have eq39041 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq39001 eq249
    | exact resolve eq249 eq39001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq39001
  have eq40356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39041 eq37738
    | exact resolve eq37738 eq39041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37738 eq39041
  have eq40357 : False := by grind
  exact eq40357
