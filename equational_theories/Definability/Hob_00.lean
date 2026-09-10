import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3929`: `x ◇ y = (x ◇ (y ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxy_pxx_x_Equation3929 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law3929 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3929.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq26 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 X1)) X2 X3
       have i₂ := eq9 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq63 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq63 X0 X1 X2
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 x (M.op X0 X1)
       have r₂ := eq63 X0 X1 x
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq84 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq82 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq865 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq865 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq865 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq865 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq909 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 (σ X0) X1
       have i₂ := eq866 (σ X0)
       grind)
    | exact superpose eq866 eq26
    | exact resolve eq26 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq922 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq909 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq909
    | exact resolve eq909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq949 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq922 X0 X1
       have i₂ := eq866 X0
       grind)
    | exact superpose eq866 eq922
    | exact resolve eq922 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq922
  have eq971 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq949 X0 X1
       have i₂ := eq84 X0 X0 X1
       grind)
    | exact superpose eq84 eq949
    | exact resolve eq949 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq989 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq971 X0 X1
       have i₂ := eq67 X1 X0
       grind)
    | exact superpose eq67 eq971
    | exact resolve eq971 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq1001 : ∀ X0 X1 : G, (M.op (σ X1) (M.op (σ X0) (σ X0))) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq989 X0 X1
       have i₂ := eq84 (σ X0) (σ X0) (σ X1)
       grind)
    | exact superpose eq84 eq989
    | exact resolve eq989 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq989
  have eq1011 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1001 X0 X1
       have i₂ := eq67 (σ X1) (σ X0)
       grind)
    | exact superpose eq67 eq1001
    | exact resolve eq1001 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq1001
  have eq1114 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1011 y x
       grind)
    | exact superpose eq1011 eq16
    | (have r₁ := eq16
       have r₂ := eq1011 y x
       grind)
    | exact resolve eq16 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1136 : False := by grind
  exact eq1136

/-- `Equation4467`: `x ◇ (y ◇ x) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4467 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4467 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4467.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq13 X0 (k (M.op X0 X0) X1)
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
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
  have eq175 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq91 (M.op sF2 sF2)
       have i₂ := eq175 sF2
       grind)
    | exact superpose eq175 eq91
    | exact resolve eq91 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq200 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq30 eq189
    | exact resolve eq189 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq207 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq108 (M.op sF3 sF3)
       have i₂ := eq175 sF3
       grind)
    | exact superpose eq175 eq108
    | exact resolve eq108 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq175
  have eq218 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq32 eq207
    | exact resolve eq207 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq318 : ∀ X0 : G, (k (k (σ x) (σ y)) (σ X0)) = (σ (k (k x y) X0)) := by
    intro X0
    first
    | exact superpose eq99 eq35
    | exact resolve eq35 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq336
    | exact resolve eq336 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq604 : ∀ X0 : G, (τ (k (k (σ x) (σ y)) X0)) = (k (k x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq99 eq427
    | exact resolve eq427 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq427
  have eq692 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op X0 (M.op X1 X0)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq16 X2 X3 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq692 x x X2 X3 X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq692
    | exact resolve eq692 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq699 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq696 x x X5
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq696
    | exact resolve eq696 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq700 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (M.op X0 X1) (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq693 (M.op X0 X1) X1
       have i₂ := eq693 X1 X0
       grind)
    | exact superpose eq693 eq693
    | exact resolve eq693 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq693 x x
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq708 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op X0 X1) (M.op (M.op x y) y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) X1 X2 X3
       have i₂ := eq693 X1 X0
       grind)
    | exact superpose eq693 eq16
    | exact resolve eq16 eq693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq693
    | exact resolve eq693 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq728 eq699
    | exact resolve eq699 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq699 eq28
    | (have j0 := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq699 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq28 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq757 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq770 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq728 eq765
    | exact resolve eq765 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq775 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq770 eq35
    | exact resolve eq35 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq788 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq775 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq775
    | exact resolve eq775 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq801 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq28
    | (have j0 := eq28 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq28 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq28 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (k (M.op X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X3 X0 X1
       have i₂ := eq11 (M.op X0 X1) X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X1 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq811 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq699 x
       have i₂ := eq11 (M.op sF4 sF3) x
       grind)
    | exact superpose eq11 eq699
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq699 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq828 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq840 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq801 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq850 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq811 X0
       have j1 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq811 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq811 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq811 x
       have r₂ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) x
       grind)
    | exact resolve eq811 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq851 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq810 X0 X1 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq810
    | (have j0 := eq810 X0 X1 x x
       grind)
    | exact resolve eq810 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq855 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq805 X0 X1 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq805
    | (have j0 := eq805 X1 X1 x x
       grind)
    | exact resolve eq805 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq857 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq840 X0 X1
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq840 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq840 X1 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq840 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq867 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq850 X0
       have j1 := eq28 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq850 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq850 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq868 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (k (M.op X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq728 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq869 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (M.op (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq728 eq855
    | (have j0 := eq855 X1 X1
       grind)
    | exact resolve eq855 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq872 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq728 eq867
    | exact resolve eq867 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq875 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq829 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq829
    | (have j0 := eq829 (σ X0)
       grind)
    | exact resolve eq829 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq788 eq829
    | (have j0 := eq829 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq829 (σ (M.op (M.op x y) y))
       have r₂ := eq788 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq829 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq921 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq908
  have eq998 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq693 X0 (M.op x X0)
       have i₂ := eq706 x X0
       grind)
    | (have i₁ := eq693 y (M.op x y)
       have i₂ := eq706 x x
       grind)
    | exact superpose eq706 eq693
    | exact resolve eq693 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) y)) (σ (M.op x y))) := by
    first
    | exact superpose eq872 eq42
    | exact resolve eq42 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1041 : (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) y) := by
    first
    | exact superpose eq872 eq153
    | exact resolve eq153 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq2918 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq814
       grind)
    | exact superpose eq814 eq41
    | exact resolve eq41 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2919 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2918
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2918
    | exact resolve eq2918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2918
  have eq2921 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq2919
    | exact resolve eq2919 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919
  have eq5413 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (k X0 X1) (k X0 X1)) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X1) X1
       have i₂ := eq869 X0 X1
       grind)
    | exact superpose eq869 eq11
    | (have j0 := eq11 X1 X1
       have j1 := eq869 X1 X1
       grind)
    | exact resolve eq11 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5434 : ∀ X0 X1 : G, (M.op (M.op x y) y) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 ∨ (M.op (k X0 X1) (k X0 X1)) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5413
  have eq5522 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k (σ (M.op X0 (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq42 (M.op X0 sF0)
       have i₂ := eq868 X0 sF0
       grind)
    | exact superpose eq868 eq42
    | (have j1 := eq868 X0 (M.op x y)
       grind)
    | exact resolve eq42 eq868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq868
  have eq21134 : (M.op (M.op x y) y) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq921 eq706
    | exact resolve eq706 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21135 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0 X1
    first
    | exact superpose eq921 eq708
    | exact resolve eq708 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq21142 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) y)) = (σ (M.op (M.op x y) y)) := by
    intro X0 X1
    first
    | exact superpose eq921 eq21135
    | exact resolve eq21135 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21135
  have eq21157 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq700 eq21142
    | exact resolve eq21142 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21142
  have eq21213 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq21157 eq15
    | exact resolve eq15 eq21157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2921 eq821
    | exact resolve eq821 eq2921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23785 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23777
       have r₂ := eq27
       grind)
    | exact resolve eq23777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23777
  have eq23792 : y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23785 eq218
    | exact resolve eq218 eq23785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23785
  have eq23829 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq23792
    | exact resolve eq23792 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23792
  have eq23842 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq23829
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq23829
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq23829
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23829 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23829
  have eq23849 : x = (k x (τ (σ y))) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23842 eq200
    | exact resolve eq200 eq23842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq23842
  have eq23887 : x = (k x y) ∨ y = (k y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq23849
    | exact resolve eq23849 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23849
  have eq23896 : x = (k x y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq857 y x
       grind)
    | (have r₁ := eq23887
       have r₂ := eq857 y x
       grind)
    | exact resolve eq23887 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23887
  have eq23899 : x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq23896
       have r₂ := eq13 x y
       grind)
    | exact resolve eq23896 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23896
  have eq23903 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq814
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq814
    | exact resolve eq814 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq23905 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq41
    | exact resolve eq41 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23906 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq869 x y
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq869
    | (have j0 := eq869 y y
       grind)
    | exact resolve eq869 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23907 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq23906
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23906
    | exact resolve eq23906 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23906
  have eq23908 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq23905
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23905
    | exact resolve eq23905 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23905
  have eq23915 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23908 eq2921
    | exact resolve eq2921 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921
  have eq23918 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23908 eq821
    | exact resolve eq821 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq23922 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23908 eq869
    | (have j0 := eq869 (σ y) (σ y)
       grind)
    | exact resolve eq869 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq23923 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq23922
    | exact resolve eq23922 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23922
  have eq23929 : (σ x) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23918 eq23923
    | exact resolve eq23923 eq23918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23923
  have eq23934 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq23903
       grind)
    | exact superpose eq23903 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq23903
       grind)
    | exact resolve eq28 eq23903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23949 : (M.op y y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq23903
       grind)
    | exact superpose eq23903 eq706
    | exact resolve eq706 eq23903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23952 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq23934 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23934
  have eq23955 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23903 eq23949
    | exact resolve eq23949 eq23903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23903 eq23949
  have eq23988 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq23915
       grind)
    | exact superpose eq23915 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq23915
       grind)
    | exact resolve eq28 eq23915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24003 : (M.op y y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq23915
       grind)
    | exact superpose eq23915 eq706
    | exact resolve eq706 eq23915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24006 : ∀ X0 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq23988 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23988
  have eq24009 : y = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23915 eq24003
    | exact resolve eq24003 eq23915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23915 eq24003
  have eq24040 : y = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23918 eq218
    | exact resolve eq218 eq23918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq24057 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23918 eq706
    | exact resolve eq706 eq23918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24064 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq23918 eq24057
    | exact resolve eq24057 eq23918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23918 eq24057
  have eq24077 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq32 eq24040
    | exact resolve eq24040 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24040
  have eq24106 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq23952 X0
       grind)
    | exact superpose eq23952 eq693
    | (have j1 := eq23952 X0
       grind)
    | exact resolve eq693 eq23952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23952
  have eq24127 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq24106 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24106
    | (have j0 := eq24106 X0
       grind)
    | exact resolve eq24106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24106
  have eq24175 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq23955 eq998
    | exact resolve eq998 eq23955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24227 : y = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23955 eq21157
    | exact resolve eq21157 eq23955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24264 : y = (M.op x x) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq24227
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24227
    | exact resolve eq24227 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24227
  have eq24421 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq24264
       grind)
    | exact superpose eq24264 eq693
    | exact resolve eq693 eq24264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24442 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq24421
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24421
    | exact resolve eq24421 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24421
  have eq24482 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq24442 eq872
    | exact resolve eq872 eq24442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24561 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (σ y) := by
    first
    | exact superpose eq24442 eq700
    | exact resolve eq700 eq24442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq26602 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq24006 X0
       grind)
    | exact superpose eq24006 eq693
    | (have j1 := eq24006 X0
       grind)
    | exact resolve eq693 eq24006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24006
  have eq26623 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq26602 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26602
    | (have j0 := eq26602 X0
       grind)
    | exact resolve eq26602 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26602
  have eq26673 : ∀ X0 : G, y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq24009 eq998
    | exact resolve eq998 eq24009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26725 : y = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq24009 eq21157
    | exact resolve eq21157 eq24009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24009
  have eq26764 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq26725
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26725
    | exact resolve eq26725 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26725
  have eq26921 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq26764
       grind)
    | exact superpose eq26764 eq693
    | exact resolve eq693 eq26764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26764
  have eq26942 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq26921
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26921
    | exact resolve eq26921 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26921
  have eq27044 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq26942 eq21157
    | exact resolve eq21157 eq26942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27080 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq27044
    | exact resolve eq27044 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27044
  have eq27419 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by grind
  have eq28758 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq24064 eq693
    | exact resolve eq693 eq24064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24064
  have eq28780 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq26 eq28758
    | exact resolve eq28758 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28758
  have eq28808 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq24077 eq693
    | exact resolve eq693 eq24077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24077
  have eq28830 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq26 eq28808
    | exact resolve eq28808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28808
  have eq28870 : ∀ X0 X1 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq872 X0
       have i₂ := eq24127 (M.op sF0 y)
       grind)
    | exact superpose eq24127 eq872
    | (have j1 := eq24127 X1
       grind)
    | exact resolve eq872 eq24127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq24127
  have eq29006 : ∀ X0 X1 : G, (M.op x y) = (k (M.op x y) X0) ∨ x = (M.op x y) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq24482 eq28870
    | (have j0 := eq28870 X0 X1
       have j1 := eq24482 X0
       grind)
    | exact resolve eq28870 eq24482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24482 eq28870
  have eq30665 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq24175 X0
       grind)
    | exact superpose eq24175 eq693
    | (have j1 := eq24175 X0
       grind)
    | exact resolve eq693 eq24175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24175
  have eq30688 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq30665 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30665
    | (have j0 := eq30665 X0
       grind)
    | exact resolve eq30665 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30665
  have eq30705 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq24442 eq30688
    | exact resolve eq30688 eq24442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24442 eq30688
  have eq31099 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1038
       have i₂ := eq26623 (M.op sF0 y)
       grind)
    | exact superpose eq26623 eq1038
    | (have j1 := eq26623 X0
       grind)
    | exact resolve eq1038 eq26623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq31146 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq21157
       have i₂ := eq26623 (M.op sF0 y)
       grind)
    | exact superpose eq26623 eq21157
    | (have j1 := eq26623 X0
       grind)
    | exact resolve eq21157 eq26623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26623
  have eq31184 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq31146
    | (have j0 := eq31146 X0
       grind)
    | exact resolve eq31146 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31146
  have eq31209 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq31099
    | (have j0 := eq31099 X0
       grind)
    | exact resolve eq31099 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31099
  have eq31243 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq27080 eq31184
    | exact resolve eq31184 eq27080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31184
  have eq31266 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31243 eq829
    | (have j0 := eq829 (σ y)
       grind)
    | (have r₁ := eq829 (σ y)
       have r₂ := eq31243 (σ y)
       grind)
    | exact resolve eq829 eq31243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31348 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq31266
  have eq31503 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31348 eq706
    | exact resolve eq706 eq31348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31510 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq27080 eq31503
    | exact resolve eq31503 eq27080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27080 eq31503
  have eq31525 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq31348 eq31510
    | exact resolve eq31510 eq31348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31348 eq31510
  have eq32447 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq26673 X0
       grind)
    | exact superpose eq26673 eq693
    | (have j1 := eq26673 X0
       grind)
    | exact resolve eq693 eq26673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26673
  have eq32470 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq32447 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32447
    | (have j0 := eq32447 X0
       grind)
    | exact resolve eq32447 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32447
  have eq32487 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq26942 eq32470
    | exact resolve eq32470 eq26942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26942 eq32470
  have eq37669 : ∀ X0 : G, (σ y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq28780 eq770
    | exact resolve eq770 eq28780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28780
  have eq38095 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq28830 eq1041
    | exact resolve eq1041 eq28830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq28830
  have eq38237 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq857 y (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq38095
       have r₂ := eq857 y x
       grind)
    | exact resolve eq38095 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38095
  have eq38453 : (σ (τ (M.op (σ x) (σ y)))) = (k (σ (τ (M.op (σ x) (σ y)))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38237 eq41
    | exact resolve eq41 eq38237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq38237
  have eq38463 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38453
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq38453
    | exact resolve eq38453 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38453
  have eq39283 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k (M.op x y) (σ y)) := by
    first
    | (have j0 := eq29006 (σ y) (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29006
  have eq39284 : (M.op x y) = (k (M.op x y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq39283
  have eq39859 : (σ (M.op (M.op x y) y)) = (k (k (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq318 y
       have i₂ := eq5434 x y
       grind)
    | exact superpose eq5434 eq318
    | (have j1 := eq5434 x y
       grind)
    | exact resolve eq318 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq39871 : (τ (M.op (M.op x y) y)) = (k (k x y) (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq604 sF3
       have i₂ := eq5434 sF2 sF3
       grind)
    | exact superpose eq5434 eq604
    | (have j1 := eq5434 (σ x) (σ y)
       grind)
    | exact resolve eq604 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq5434
  have eq40167 : (τ (M.op (M.op x y) y)) = (k (k x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq39871
    | exact resolve eq39871 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39871
  have eq40179 : (σ (M.op (M.op x y) y)) = (k (k (σ x) (σ y)) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39859
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq39859
    | exact resolve eq39859 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39859
  have eq40336 : (k x y) = (τ (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq40167
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq40167
    | exact resolve eq40167 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40167
  have eq40348 : (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23908 eq40179
    | exact resolve eq40179 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40179
  have eq40389 : (k x y) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq21213 eq40336
    | exact resolve eq40336 eq21213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40336
  have eq40392 : (k (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21157 eq40348
    | exact resolve eq40348 eq21157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40348
  have eq40411 : x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq40389
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq40389
    | exact resolve eq40389 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40389
  have eq40413 : (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op (k x y) (k x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23908 eq40392
    | exact resolve eq40392 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40392
  have eq40426 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23908 eq40411
    | exact resolve eq40411 eq23908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23908 eq40411
  have eq40427 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq40426
  have eq40428 : y = (M.op x x) ∨ (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq40413
       have i₂ := eq23899
       grind)
    | exact superpose eq23899 eq40413
    | exact resolve eq40413 eq23899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23899 eq40413
  have eq40429 : y = (M.op x x) ∨ (σ x) = (M.op (M.op x y) y) ∨ y = (M.op y y) := by grind
  clear eq40428
  have eq40436 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq23929 eq40427
    | exact resolve eq40427 eq23929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23929 eq40427
  have eq40437 : y = (M.op y y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23907 eq40429
    | exact resolve eq40429 eq23907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23907 eq40429
  have eq40876 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40436 eq706
    | exact resolve eq706 eq40436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40883 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (σ x) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq40436 eq40876
    | exact resolve eq40876 eq40436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40436 eq40876
  have eq40917 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq28 X0 y
       have i₂ := eq40437
       grind)
    | exact superpose eq40437 eq28
    | (have j0 := eq28 X0 y
       grind)
    | (have r₁ := eq28 X0 y
       have r₂ := eq40437
       grind)
    | exact resolve eq28 eq40437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40932 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq706 y y
       have i₂ := eq40437
       grind)
    | exact superpose eq40437 eq706
    | exact resolve eq706 eq40437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40935 : ∀ X0 : G, y = (M.op x x) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq40917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40917
  have eq40938 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40437 eq40932
    | exact resolve eq40932 eq40437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40437 eq40932
  have eq41029 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq40883 eq693
    | exact resolve eq693 eq40883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40883
  have eq41051 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq26 eq41029
    | exact resolve eq41029 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41029
  have eq41130 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq693 x x
       have i₂ := eq40935 X0
       grind)
    | exact superpose eq40935 eq693
    | (have j1 := eq40935 X0
       grind)
    | exact resolve eq693 eq40935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40935
  have eq41151 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq41130 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41130
    | (have j0 := eq41130 X0
       grind)
    | exact resolve eq41130 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41130
  have eq41191 : ∀ X0 : G, y = (M.op y X0) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq40938 eq751
    | exact resolve eq751 eq40938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41203 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40938 eq921
    | exact resolve eq921 eq40938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41265 : y = (σ y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq40938 eq21157
    | exact resolve eq21157 eq40938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41288 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq40938 eq695
    | exact resolve eq695 eq40938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq40938
  have eq41309 : (M.op y y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41288 x x
       have i₂ := eq694 x x
       grind)
    | exact superpose eq694 eq41288
    | exact resolve eq41288 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq41288
  have eq41317 : y = (M.op x x) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq41265
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41265
    | exact resolve eq41265 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41265
  have eq41376 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41203
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq41203
    | exact resolve eq41203 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41203
  have eq41394 : (M.op y y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq728 eq41309
    | exact resolve eq41309 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41309
  have eq41426 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq41317 eq41394
    | exact resolve eq41394 eq41317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41394
  have eq41449 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq41376 eq41426
    | exact resolve eq41426 eq41376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41376 eq41426
  have eq41530 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq41317
       grind)
    | exact superpose eq41317 eq693
    | exact resolve eq693 eq41317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41551 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq41530
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41530
    | exact resolve eq41530 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41530
  have eq41590 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq41551 eq751
    | exact resolve eq751 eq41551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41664 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq41551 eq21157
    | exact resolve eq21157 eq41551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41710 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq41664
    | exact resolve eq41664 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41664
  have eq41789 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | (have r₁ := eq41710
       have r₂ := eq27419
       grind)
    | exact resolve eq41710 eq27419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27419 eq41710
  have eq41850 : (M.op x y) = (τ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq41789 eq29
    | exact resolve eq29 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq50568 : ∀ X0 : G, (σ y) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq41051 eq770
    | exact resolve eq770 eq41051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51616 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq921
       have i₂ := eq41151 (M.op sF0 y)
       grind)
    | exact superpose eq41151 eq921
    | (have j1 := eq41151 X0
       grind)
    | exact resolve eq921 eq41151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51678 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq21157
       have i₂ := eq41151 (M.op sF0 y)
       grind)
    | exact superpose eq41151 eq21157
    | (have j1 := eq41151 X0
       grind)
    | exact resolve eq21157 eq41151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41151
  have eq51736 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq51678
    | (have j0 := eq51678 X0
       grind)
    | exact resolve eq51678 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51678
  have eq51770 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq51616
    | (have j0 := eq51616 X0
       grind)
    | exact resolve eq51616 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51616
  have eq51803 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq41789 eq51736
    | exact resolve eq51736 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51736
  have eq52008 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq51803 eq829
    | (have j0 := eq829 (σ y)
       grind)
    | (have r₁ := eq829 (σ y)
       have r₂ := eq51803 (σ y)
       grind)
    | exact resolve eq829 eq51803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52099 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq52008
  have eq53058 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 y) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq693 X0 y
       have i₂ := eq41191 X0
       grind)
    | exact superpose eq41191 eq693
    | exact resolve eq693 eq41191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41191
  have eq53111 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq41317 eq53058
    | exact resolve eq53058 eq41317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41317 eq53058
  have eq53137 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq41449 eq53111
    | exact resolve eq53111 eq41449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41449 eq53111
  have eq57592 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (k X1 (M.op (σ x) (σ y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq998 X0
       have i₂ := eq50568 (M.op sF0 y)
       grind)
    | exact superpose eq50568 eq998
    | (have j1 := eq50568 X1
       grind)
    | exact resolve eq998 eq50568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998 eq50568
  have eq66265 : y = (M.op x x) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53137 eq26
    | (have j1 := eq53137 (σ x)
       grind)
    | exact resolve eq26 eq53137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53137
  have eq66398 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq66265
       grind)
    | exact superpose eq66265 eq693
    | exact resolve eq693 eq66265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66419 : (M.op x y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66398
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66398
    | exact resolve eq66398 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66398
  have eq66545 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66419 eq21157
    | exact resolve eq21157 eq66419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66602 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq66545
    | exact resolve eq66545 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66545
  have eq66892 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) X0) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq66602 eq699
    | exact resolve eq699 eq66602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66986 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq52099 eq66892
    | exact resolve eq66892 eq52099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52099 eq66892
  have eq68367 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) (σ y)) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq66986 eq11
    | (have j0 := eq11 X0 X0
       grind)
    | exact resolve eq11 eq66986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66986
  have eq68451 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq68367 X0
       have j1 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq68367 x
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq68367 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq68367 x
       have r₂ := eq13 (σ y) x
       grind)
    | exact resolve eq68367 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68367
  have eq68486 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq68451 X0
       have j1 := eq28 (σ y) X0
       grind)
    | (have r₁ := eq68451 x
       have r₂ := eq28 X0 x
       grind)
    | exact resolve eq68451 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68451
  have eq72403 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq57592 X0 (M.op sF2 sF3)
       grind)
    | exact superpose eq57592 eq26
    | (have j1 := eq57592 (σ x) X0
       grind)
    | exact resolve eq26 eq57592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57592
  have eq72513 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72403 eq829
    | (have j0 := eq829 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq829 (M.op (σ x) (σ y))
       have r₂ := eq72403 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq829 eq72403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72403
  have eq72575 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq72513
  have eq72710 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72575 eq706
    | exact resolve eq706 eq72575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72718 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72575 eq72710
    | exact resolve eq72710 eq72575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72575 eq72710
  have eq72862 : y = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72718 eq23955
    | exact resolve eq23955 eq72718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23955
  have eq72940 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24264 eq72862
    | exact resolve eq72862 eq24264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24264 eq72862
  have eq72941 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (σ x) := by grind
  clear eq72940
  have eq73034 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66265 eq72941
    | exact resolve eq72941 eq66265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66265 eq72941
  have eq73035 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq73034
  have eq74559 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq693 x x
       have i₂ := eq73035
       grind)
    | exact superpose eq73035 eq693
    | exact resolve eq693 eq73035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73035
  have eq74580 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74559
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq74559
    | exact resolve eq74559 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74559
  have eq74725 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq74580 eq72718
    | exact resolve eq72718 eq74580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72718 eq74580
  have eq74747 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq74725
  have eq77776 : (M.op x y) ≠ (σ y) ∨ x = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq74747
  have eq83592 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq829 X0
       have i₂ := eq31209 (k X0 X0)
       grind)
    | exact superpose eq31209 eq829
    | (have j0 := eq829 (σ (M.op x y))
       have j1 := eq31209 X0
       grind)
    | (have r₁ := eq829 (σ (M.op x y))
       have r₂ := eq31209 X0
       grind)
    | (have r₁ := eq829 y
       have r₂ := eq31209 y
       grind)
    | exact resolve eq829 eq31209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31209
  have eq83614 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq83592 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83592
  have eq83621 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq51770 eq83614
    | (have j0 := eq83614 X0
       have j1 := eq51770 X0
       grind)
    | exact resolve eq83614 eq51770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51770 eq83614
  have eq83632 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq41789 eq83621
    | exact resolve eq83621 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83621
  have eq83639 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq31243 eq83632
    | (have j0 := eq83632 X0
       have j1 := eq31243 X0
       grind)
    | exact resolve eq83632 eq31243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31243 eq83632
  have eq83643 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq51803 eq83639
    | (have j0 := eq83639 X0
       have j1 := eq51803 X0
       grind)
    | exact resolve eq83639 eq51803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51803 eq83639
  have eq86777 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq32487 eq26
    | (have j1 := eq32487 (σ x)
       grind)
    | exact resolve eq26 eq32487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32487
  have eq86808 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq66419 eq86777
    | exact resolve eq86777 eq66419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66419 eq86777
  have eq86859 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41789 eq86808
    | exact resolve eq86808 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86808
  have eq86947 : (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86859 eq31525
    | exact resolve eq31525 eq86859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31525
  have eq86972 : (M.op (M.op x y) y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86859 eq693
    | exact resolve eq693 eq86859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86992 : (M.op x y) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq86947
  have eq87009 : (M.op (σ y) (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41789 eq86972
    | exact resolve eq86972 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86972
  have eq87019 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66602 eq86992
    | exact resolve eq86992 eq66602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66602 eq86992
  have eq87020 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq87019
  have eq87031 : (M.op x y) = (M.op (σ y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86859 eq87009
    | exact resolve eq87009 eq86859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87009
  have eq87041 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87020 eq87031
    | exact resolve eq87031 eq87020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87031
  have eq87071 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq87020 eq38463
    | exact resolve eq38463 eq87020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38463 eq87020
  have eq87180 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq68486 eq87071
    | (have j1 := eq68486 (σ y)
       grind)
    | exact resolve eq87071 eq68486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68486 eq87071
  have eq87181 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq87180
  have eq87527 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq87041 eq28
    | (have j0 := eq28 X0 (M.op x y)
       grind)
    | (have r₁ := eq28 X0 (M.op x y)
       have r₂ := eq87041
       grind)
    | exact resolve eq28 eq87041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87041
  have eq87549 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq87527 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87527
  have eq87601 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87549 eq875
    | (have j0 := eq875 (M.op x y)
       grind)
    | exact resolve eq875 eq87549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875 eq87549
  have eq87667 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq87601
  have eq87722 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq87667
    | exact resolve eq87667 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87667
  have eq87816 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq87181 eq857
    | (have j0 := eq857 (σ y) X0
       grind)
    | (have r₁ := eq857 (σ y) x
       have r₂ := eq87181
       grind)
    | exact resolve eq857 eq87181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857 eq87181
  have eq87834 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq87816 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87816
  have eq88437 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq87722 eq706
    | exact resolve eq706 eq87722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88454 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41789 eq88437
    | exact resolve eq88437 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88437
  have eq88471 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq86859 eq88454
    | exact resolve eq88454 eq86859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86859 eq88454
  have eq89746 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq88471 eq87722
    | exact resolve eq87722 eq88471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87722 eq88471
  have eq89774 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq89746
  have eq89799 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq89774 eq699
    | exact resolve eq699 eq89774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq89804 : (M.op (σ y) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq89774 eq728
    | exact resolve eq728 eq89774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89774
  have eq89930 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41789 eq89804
    | exact resolve eq89804 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89804
  have eq90042 : ∀ X0 : G, (σ y) ≠ (M.op (M.op x y) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq89930 eq28
    | (have j0 := eq28 X0 (σ y)
       grind)
    | exact resolve eq28 eq89930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq90089 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq87834 eq90042
    | (have j0 := eq90042 X0
       have j1 := eq87834 X0
       grind)
    | exact resolve eq90042 eq87834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87834 eq90042
  have eq90099 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq90089 X0
       have j1 := eq83643 X0
       grind)
    | (have r₁ := eq90089 X0
       have r₂ := eq83643 X0
       grind)
    | exact resolve eq90089 eq83643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83643 eq90089
  have eq90130 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq90099 eq829
    | (have j0 := eq829 (σ y)
       grind)
    | (have r₁ := eq829 (σ y)
       have r₂ := eq90099 (σ y)
       grind)
    | exact resolve eq829 eq90099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90099
  have eq90225 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq90130
  have eq90393 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq90225 eq89930
    | exact resolve eq89930 eq90225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89930
  have eq90418 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq90393
  have eq95873 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq90225 eq89799
    | exact resolve eq89799 eq90225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89799 eq90225
  have eq96051 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq95873 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95873
  have eq96513 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq96051 eq693
    | exact resolve eq693 eq96051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq96596 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq41789 eq96513
    | exact resolve eq96513 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96513
  have eq96634 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq90418 eq96596
    | exact resolve eq96596 eq90418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90418 eq96596
  have eq100234 : ∀ X0 : G, (σ y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq21213
       have i₂ := eq37669 (M.op sF0 y)
       grind)
    | exact superpose eq37669 eq21213
    | (have j1 := eq37669 X0
       grind)
    | exact resolve eq21213 eq37669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21213 eq37669
  have eq100325 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq32 eq100234
    | (have j0 := eq100234 X0
       grind)
    | exact resolve eq100234 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq100234
  have eq100571 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq100325 eq829
    | (have j0 := eq829 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq829 (M.op (σ x) (σ y))
       have r₂ := eq100325 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq829 eq100325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100325
  have eq100635 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq100571
  have eq101965 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq100635 eq706
    | exact resolve eq706 eq100635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101980 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq100635 eq101965
    | exact resolve eq101965 eq100635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100635 eq101965
  have eq102150 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq101980 eq41590
    | exact resolve eq41590 eq101980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41590 eq101980
  have eq102183 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq102150
  have eq103961 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq102183 eq728
    | exact resolve eq728 eq102183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728 eq102183
  have eq104062 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq103961
    | exact resolve eq103961 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103961
  have eq104073 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41551 eq104062
    | exact resolve eq104062 eq41551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41551 eq104062
  have eq104074 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by grind
  clear eq104073
  have eq104086 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq104074 eq27
    | exact resolve eq27 eq104074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104074
  have eq104252 : (M.op x y) = (σ x) ∨ y = (σ y) := by
    first
    | (have r₁ := eq104086
       have r₂ := eq41789
       grind)
    | exact resolve eq104086 eq41789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41789 eq104086
  have eq104259 : x = (τ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq104252 eq30
    | exact resolve eq30 eq104252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq104252
  have eq104408 : y = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq41850 eq104259
    | exact resolve eq104259 eq41850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41850 eq104259
  have eq104468 : (M.op x y) = (M.op x (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq104408
       grind)
    | exact superpose eq104408 eq18
    | exact resolve eq18 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104469 : (σ y) = (σ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq104408
       grind)
    | exact superpose eq104408 eq24
    | exact resolve eq24 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq104501 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op (M.op (M.op x y) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq751 X0
       have i₂ := eq104408
       grind)
    | exact superpose eq104408 eq751
    | exact resolve eq751 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104502 : ∀ X0 : G, (k X0 (M.op (M.op x y) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq770 X0
       have i₂ := eq104408
       grind)
    | exact superpose eq104408 eq770
    | exact resolve eq770 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq105471 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104468 eq30705
    | exact resolve eq30705 eq104468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30705
  have eq105483 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104468 eq96634
    | exact resolve eq96634 eq104468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96634
  have eq105512 : (M.op x y) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) := by grind
  clear eq105471
  have eq105535 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq104408 eq105512
    | exact resolve eq105512 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105512
  have eq105947 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq105483 eq96051
    | exact resolve eq96051 eq105483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96051
  have eq105953 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105483 eq104469
    | exact resolve eq104469 eq105483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104469 eq105483
  have eq105959 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq105953
  have eq105963 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq105947 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105947
  have eq106056 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq105959
    | exact resolve eq105959 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105959
  have eq106057 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq106056
  have eq109141 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq105535 eq104502
    | exact resolve eq104502 eq105535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104502
  have eq109198 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq109141 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109141
  have eq109360 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq109198 eq829
    | (have j0 := eq829 (M.op x y)
       grind)
    | (have r₁ := eq829 (M.op x y)
       have r₂ := eq109198 (M.op x y)
       grind)
    | exact resolve eq829 eq109198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109198
  have eq109433 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by grind
  clear eq109360
  have eq114694 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq105535 eq104501
    | exact resolve eq104501 eq105535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105535
  have eq114718 : ∀ X0 : G, (k (M.op x y) (σ y)) = (M.op (k (M.op x y) (σ y)) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq104501 X0
       have i₂ := eq11 sF0 sF3
       grind)
    | exact superpose eq11 eq104501
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq104501 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114827 : (σ (M.op (M.op x y) y)) = (k (σ (M.op (M.op x y) (σ y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104501 eq5522
    | exact resolve eq5522 eq104501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5522
  have eq114879 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq114694 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114694
  have eq114889 : (M.op (M.op x y) y) = (k (σ (M.op (M.op x y) (σ y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21157 eq114827
    | exact resolve eq114827 eq21157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21157 eq114827
  have eq114936 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq39284 eq114718
    | exact resolve eq114718 eq39284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39284 eq114718
  have eq114940 : (M.op (M.op x y) (σ y)) = (k (σ (M.op (M.op x y) (σ y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq24561 eq114889
    | exact resolve eq114889 eq24561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24561 eq114889
  have eq114965 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq114879 eq114936
    | (have j0 := eq114936 X0
       have j1 := eq114879 X0
       grind)
    | exact resolve eq114936 eq114879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114936
  have eq114966 : (M.op (M.op x y) (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (σ y)) (M.op (M.op x y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq109433 eq114940
    | exact resolve eq114940 eq109433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114940
  have eq114976 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq114879 eq114965
    | (have j0 := eq114965 X0
       have j1 := eq114879 X0
       grind)
    | exact resolve eq114965 eq114879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114879 eq114965
  have eq114977 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq114976 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114976
  have eq114978 : (M.op (M.op x y) (M.op x y)) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq109433 eq114966
    | exact resolve eq114966 eq109433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109433 eq114966
  have eq114980 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114977 eq114978
    | (have j1 := eq114977 (M.op x y)
       grind)
    | exact resolve eq114978 eq114977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114978
  have eq114981 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq114980
    | exact resolve eq114980 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114980
  have eq114982 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114977 eq114981
    | (have j1 := eq114977 (M.op x y)
       grind)
    | exact resolve eq114981 eq114977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114977 eq114981
  have eq114983 : (M.op x y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq114982
  have eq114984 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105963 eq114983
    | (have j1 := eq105963 (M.op x y)
       grind)
    | exact resolve eq114983 eq105963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105963 eq114983
  have eq114985 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq114984
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq114984 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114984
  have eq114995 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114985 eq829
    | (have j0 := eq829 (M.op x y)
       grind)
    | (have r₁ := eq829 (M.op x y)
       have r₂ := eq114985
       grind)
    | exact resolve eq829 eq114985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq829 eq114985
  have eq115017 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq114995
  have eq115319 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115017 eq706
    | exact resolve eq706 eq115017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq115334 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104408 eq115319
    | exact resolve eq115319 eq104408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104408 eq115319
  have eq115351 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115017 eq115334
    | exact resolve eq115334 eq115017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115017 eq115334
  have eq115424 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq115351 eq104501
    | exact resolve eq104501 eq115351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104501 eq115351
  have eq115473 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq115424 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115424
  have eq115691 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115473 eq41051
    | exact resolve eq41051 eq115473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41051 eq115473
  have eq115853 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq115691
       have r₂ := eq77776
       grind)
    | exact resolve eq115691 eq77776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77776 eq115691
  have eq116646 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq115853 eq27
    | exact resolve eq27 eq115853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115853
  have eq116843 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq116646
       have r₂ := eq106057
       grind)
    | exact resolve eq116646 eq106057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116646
  have eq116920 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104468
       have i₂ := eq116843
       grind)
    | exact superpose eq116843 eq104468
    | exact resolve eq104468 eq116843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104468
  have eq116928 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq116843
  have eq116932 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq116920
       have r₂ := eq116928
       grind)
    | exact resolve eq116920 eq116928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116920 eq116928
  have eq116967 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq116932
    | exact resolve eq116932 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116932
  have eq117049 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116967 eq27
    | exact resolve eq27 eq116967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116967
  have eq117185 : x = (M.op x y) := by
    first
    | (have r₁ := eq117049
       have r₂ := eq106057
       grind)
    | exact resolve eq117049 eq106057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106057 eq117049
  have eq117193 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq117185
       grind)
    | exact superpose eq117185 eq18
    | exact resolve eq18 eq117185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq117194 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq117185
       grind)
    | exact superpose eq117185 eq22
    | exact resolve eq22 eq117185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq117185
  have eq118408 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq117194 eq20
    | exact resolve eq20 eq117194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117194
  have eq119119 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq117193 eq751
    | exact resolve eq751 eq117193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq119134 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq117193 eq921
    | exact resolve eq921 eq117193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq119195 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq117193 eq21134
    | exact resolve eq21134 eq117193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21134 eq117193
  have eq119266 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq119195
    | exact resolve eq119195 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119195
  have eq119326 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq119134
    | exact resolve eq119134 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq119134
  have eq119361 : (M.op x y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq118408 eq119266
    | exact resolve eq119266 eq118408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119266
  have eq119409 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq118408 eq119326
    | exact resolve eq119326 eq118408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119326
  have eq119440 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq119361 eq119409
    | exact resolve eq119409 eq119361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119361 eq119409
  have eq119465 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq119440 eq26
    | exact resolve eq26 eq119440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq119631 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq119119 eq119465
    | exact resolve eq119465 eq119119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119119 eq119465
  have eq119878 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq119631 eq27
    | exact resolve eq27 eq119631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq119631
  have eq120008 : (M.op x y) ≠ (σ x) := by
    first
    | exact superpose eq118408 eq119878
    | exact resolve eq119878 eq118408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118408 eq119878
  have eq120015 : False := by grind
  exact eq120015

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxx_pxy_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
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
  clear eq36
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
  clear eq47
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : y ≠ (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq179 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq177 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq181 eq177
    | exact resolve eq177 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op y (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq182 eq177
    | exact resolve eq177 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq622 : (M.op x y) = (k y x) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq627 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq664 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq635 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq635 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq635 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq635 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq681 : y ≠ y ∨ y = (M.op (M.op x y) y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq181 eq12
    | (have j0 := eq12 y (M.op x y)
       grind)
    | (have r₁ := eq12 y (M.op x y)
       have r₂ := eq181
       grind)
    | exact resolve eq12 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq188 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | (have r₁ := eq12 (M.op x y) y
       have r₂ := eq188
       grind)
    | exact resolve eq12 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq182 eq12
    | (have j0 := eq12 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq182
       grind)
    | exact resolve eq12 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq191 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) (σ y)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq191
       grind)
    | exact resolve eq12 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq688
  have eq693 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq686
  have eq695 : (M.op x y) = (M.op y (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) := by grind
  clear eq683
  have eq697 : y = (M.op (M.op x y) y) ∨ y = (k y (M.op x y)) := by grind
  clear eq681
  have eq703 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq182 eq691
    | exact resolve eq691 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq705 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq191 eq693
    | exact resolve eq693 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq707 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq181 eq695
    | exact resolve eq695 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq695
  have eq709 : y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq188 eq697
    | exact resolve eq697 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq714 : (τ (σ y)) = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq705 eq107
    | exact resolve eq107 eq705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq705
  have eq715 : y = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq714
    | exact resolve eq714 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq717 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq709 eq41
    | exact resolve eq41 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq709
  have eq718 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq717
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq717
    | exact resolve eq717 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq721 : (τ (M.op (σ x) (σ y))) = (k (τ (M.op (σ x) (σ y))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq703 eq152
    | exact resolve eq152 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq703
  have eq723 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq707 eq40
    | exact resolve eq40 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq707
  have eq724 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq723
    | exact resolve eq723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq786 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq622
       grind)
    | exact superpose eq622 eq39
    | exact resolve eq39 eq622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq786
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq786
    | exact resolve eq786 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq789 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq787
    | exact resolve eq787 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq789 eq627
    | exact resolve eq627 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq831
       have r₂ := eq27
       grind)
    | exact resolve eq831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq847 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq838 eq177
    | exact resolve eq177 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838
  have eq852 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq847
    | exact resolve eq847 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq862 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq852
       grind)
    | exact superpose eq852 eq177
    | exact resolve eq177 eq852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq867 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq862
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq862
    | exact resolve eq862 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq873 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq867 eq27
    | exact resolve eq27 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq875 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq867 eq179
    | (have r₁ := eq179
       have r₂ := eq867
       grind)
    | exact resolve eq179 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq877 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq867 eq191
    | exact resolve eq191 eq867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq867
  have eq886 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq875
  have eq888 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq877 eq886
    | exact resolve eq886 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq886
  have eq909 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq888 eq789
    | exact resolve eq789 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq888
  have eq915 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq909
  have eq921 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq915
       have r₂ := eq873
       grind)
    | exact resolve eq915 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873 eq915
  have eq946 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq921
       grind)
    | exact superpose eq921 eq177
    | exact resolve eq177 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq951 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq946
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq946
    | exact resolve eq946 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946
  have eq952 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq951
  have eq961 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq952 eq182
    | exact resolve eq182 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : y = (k y (τ (σ x))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq952 eq715
    | exact resolve eq715 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq970 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq952 eq721
    | exact resolve eq721 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : x = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq970
    | exact resolve eq970 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970
  have eq974 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq969
    | exact resolve eq969 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq1101 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq664 y x
       have i₂ := eq973
       grind)
    | exact superpose eq973 eq664
    | (have j0 := eq664 y x
       grind)
    | (have r₁ := eq664 y x
       have r₂ := eq973
       grind)
    | exact resolve eq664 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq1102 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1101
  have eq1103 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1102
    | exact resolve eq1102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1104 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1103
  have eq1109 : y = (M.op x y) ∨ y = (M.op y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq622
       have i₂ := eq974
       grind)
    | exact superpose eq974 eq622
    | exact resolve eq622 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq974
  have eq1114 : y = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1109
  have eq1120 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1104 eq1114
    | exact resolve eq1114 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104 eq1114
  have eq1125 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1120 eq31
    | exact resolve eq31 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1120
  have eq1176 : x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1125
    | exact resolve eq1125 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125
  have eq1177 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1176
  have eq1182 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq24
    | exact resolve eq24 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1186 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq178
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq178
    | (have r₁ := eq178
       have r₂ := eq1177
       grind)
    | exact resolve eq178 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1188 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq188
    | exact resolve eq188 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq1198 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1186
  have eq1199 : (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1188 eq1198
    | exact resolve eq1198 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188 eq1198
  have eq1202 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1182
    | exact resolve eq1182 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1260 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1199 eq39
    | exact resolve eq39 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199
  have eq1263 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1260
    | exact resolve eq1260 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260
  have eq1265 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1202 eq1263
    | exact resolve eq1263 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1284 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1265 eq627
    | exact resolve eq627 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq1290 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1284
  have eq1297 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq961 eq1290
    | exact resolve eq1290 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq1290
  have eq1298 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1297
  have eq1330 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1298 eq177
    | exact resolve eq177 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1337 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1330
    | exact resolve eq1330 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq1342 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1337 eq27
    | exact resolve eq27 eq1337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq1361 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1202 eq1342
    | (have r₁ := eq1342
       have r₂ := eq1202
       grind)
    | exact resolve eq1342 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1362 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1361
  have eq1363 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1362
  have eq1364 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq952 eq1363
    | exact resolve eq1363 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq1365 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1364
  have eq1368 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1365 eq27
    | exact resolve eq27 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1371 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1365 eq182
    | exact resolve eq182 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1380 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1365 eq721
    | exact resolve eq721 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq1365
  have eq1384 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1380
    | exact resolve eq1380 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1380
  have eq1388 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1202 eq1368
    | exact resolve eq1368 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq1368
  have eq1389 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1388
  have eq1655 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq674 x y
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq674
    | (have j0 := eq674 x x
       grind)
    | (have r₁ := eq674 x y
       have r₂ := eq1384
       grind)
    | exact resolve eq674 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1656 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq664 y x
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq664
    | (have j0 := eq664 y x
       grind)
    | (have r₁ := eq664 y x
       have r₂ := eq1384
       grind)
    | exact resolve eq664 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384
  have eq1657 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1656
  have eq1658 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1655
  have eq1660 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1657
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1657
    | exact resolve eq1657 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1657
  have eq1661 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1660
  have eq1662 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1658
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1658
    | exact resolve eq1658 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq1663 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1662
  have eq1690 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1661
       have i₂ := eq1177
       grind)
    | exact superpose eq1177 eq1661
    | exact resolve eq1661 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1707 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1690
  have eq1712 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1707
       have r₂ := eq1389
       grind)
    | exact resolve eq1707 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707
  have eq1805 : (M.op x y) = (M.op (M.op x y) (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq190 x
       have i₂ := eq1663
       grind)
    | exact superpose eq1663 eq190
    | exact resolve eq190 eq1663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq1663
  have eq1814 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1661 eq1805
    | exact resolve eq1805 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661 eq1805
  have eq1856 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1814 eq1712
    | exact resolve eq1712 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712 eq1814
  have eq1871 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1856
  have eq1873 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1871
       have r₂ := eq1389
       grind)
    | exact resolve eq1871 eq1389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389 eq1871
  have eq1876 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq1873
       grind)
    | exact superpose eq1873 eq22
    | exact resolve eq22 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1886 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq1876
    | exact resolve eq1876 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq1898 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1886 eq718
    | exact resolve eq718 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq1899 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1886 eq724
    | exact resolve eq724 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq2051 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1898 eq627
    | exact resolve eq627 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq1898
  have eq2060 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2051
  have eq2070 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1371 eq2060
    | exact resolve eq2060 eq1371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371 eq2060
  have eq2071 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2070
  have eq2086 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1899 eq674
    | (have j0 := eq674 (σ x) (σ x)
       grind)
    | (have r₁ := eq674 (σ x) (σ y)
       have r₂ := eq1899
       grind)
    | exact resolve eq674 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq2087 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1899 eq664
    | (have j0 := eq664 (σ y) (σ x)
       grind)
    | (have r₁ := eq664 (σ y) (σ x)
       have r₂ := eq1899
       grind)
    | exact resolve eq664 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664 eq1899
  have eq2088 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2087
  have eq2089 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq2086
  have eq2091 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq2088
    | exact resolve eq2088 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088
  have eq2092 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq26 eq2089
    | exact resolve eq2089 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq2096 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq952 eq2091
    | exact resolve eq2091 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2097 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2096
  have eq2098 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq952 eq2092
    | exact resolve eq2092 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq2092
  have eq2099 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2098
  have eq2125 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2071 eq177
    | exact resolve eq177 eq2071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2071
  have eq2133 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2125
    | exact resolve eq2125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2125
  have eq2214 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2099 eq208
    | exact resolve eq208 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq2099
  have eq2218 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2133 eq2214
    | exact resolve eq2214 eq2133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133 eq2214
  have eq2221 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2097 eq2218
    | exact resolve eq2218 eq2097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2097 eq2218
  have eq2224 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2221
    | exact resolve eq2221 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq2225 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2224
  have eq2363 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2225 eq27
    | exact resolve eq27 eq2225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq2383 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1886 eq2363
    | (have r₁ := eq2363
       have r₂ := eq1886
       grind)
    | exact resolve eq2363 eq1886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886 eq2363
  have eq2385 : y = (M.op x y) ∨ x = y := by grind
  clear eq2383
  have eq2403 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq2385
  have eq2407 : x = y := by
    first
    | (have r₁ := eq2403
       have r₂ := eq1873
       grind)
    | exact resolve eq2403 eq1873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873 eq2403
  have eq2415 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2407
       grind)
    | exact superpose eq2407 eq18
    | exact resolve eq18 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2416 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2407
       grind)
    | exact superpose eq2407 eq24
    | exact resolve eq24 eq2407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2407
  have eq2450 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2416
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2416
    | exact resolve eq2416 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq2451 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2450 eq26
    | exact resolve eq26 eq2450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2450
  have eq2521 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq2415
       grind)
    | exact superpose eq2415 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2523 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq2415
       grind)
    | exact superpose eq2415 eq13
    | exact resolve eq13 eq2415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq2544 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq2521
  have eq2555 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq2544
       have r₂ := eq2523
       grind)
    | exact resolve eq2544 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523 eq2544
  have eq2600 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2451 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2602 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq2451 eq13
    | exact resolve eq13 eq2451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2451
  have eq2623 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2600
  have eq2632 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq2623
       have r₂ := eq2602
       grind)
    | exact resolve eq2623 eq2602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2602 eq2623
  have eq2681 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq2555
       grind)
    | exact superpose eq2555 eq39
    | exact resolve eq39 eq2555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2555
  have eq2693 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq2681
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2681
    | exact resolve eq2681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2681
  have eq2695 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2632 eq2693
    | exact resolve eq2693 eq2632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632 eq2693
  have eq2697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2695
    | exact resolve eq2695 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2695
  have eq2699 : False := by grind
  exact eq2699

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_y_pxy_x_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op (M.op X2 X3) (M.op X0 X3))))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op X2 X3) (M.op X0 X3))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X0) (σ X1)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq34 (τ X0)
       grind)
    | exact superpose eq34 eq19
    | exact resolve eq19 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq86
    | exact resolve eq86 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq86
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq110 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 X0 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq143 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq183 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq110 (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq110
    | exact resolve eq110 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq143
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq143
    | exact resolve eq143 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq143
  have eq601 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq562
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq562
    | (have j1 := eq59 x y
       grind)
    | exact resolve eq562 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq562
  have eq602 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq601
  have eq606 : x = (M.op x y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq110 x
       have i₂ := eq602
       grind)
    | exact superpose eq602 eq110
    | exact resolve eq110 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq183 x
       have i₂ := eq602
       grind)
    | exact superpose eq602 eq183
    | exact resolve eq183 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq6072 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq608
       grind)
    | exact superpose eq608 eq16
    | exact resolve eq16 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq6154 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6072
       have i₂ := eq606
       grind)
    | exact superpose eq606 eq6072
    | exact resolve eq6072 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq6072
  have eq6155 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq6154
  have eq6156 : (σ y) = (σ (M.op x x)) := by grind
  clear eq6155
  have eq6159 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq183 x
       have i₂ := eq6156
       grind)
    | exact superpose eq6156 eq183
    | exact resolve eq183 eq6156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq6167 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq6156
       grind)
    | exact superpose eq6156 eq10
    | exact resolve eq10 eq6156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6156
  have eq6224 : y = (M.op x x) := by
    first
    | (have i₁ := eq6167
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq6167
    | exact resolve eq6167 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6167
  have eq6426 : x = (M.op x y) := by
    first
    | (have i₁ := eq110 x
       have i₂ := eq6224
       grind)
    | exact superpose eq6224 eq110
    | exact resolve eq110 eq6224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq6224
  have eq6757 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6159
       grind)
    | exact superpose eq6159 eq16
    | exact resolve eq16 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6159
  have eq6810 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq6757
       have i₂ := eq6426
       grind)
    | exact superpose eq6426 eq6757
    | exact resolve eq6757 eq6426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6426 eq6757
  have eq6811 : False := by grind
  exact eq6811
