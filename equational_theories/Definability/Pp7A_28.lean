import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq24 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X1) (σ X0)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq22
    | exact resolve eq22 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
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
  have eq87 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq86
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq87
    | exact resolve eq87 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq87
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
  have eq109 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq23 X2 X0 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
  have eq195 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (σ X0) (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) (σ X0) X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X0) x
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq24
    | exact resolve eq24 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq168
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq168
    | (have j1 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq168 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq168
  have eq691 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq690
  have eq3785 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x y) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq24 y x x
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq24
    | exact resolve eq24 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3793 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq109 x x y
       have i₂ := eq691
       grind)
    | exact superpose eq691 eq109
    | exact resolve eq109 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq31808 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3785 (M.op y x)
       have i₂ := eq23 x y x
       grind)
    | exact superpose eq23 eq3785
    | exact resolve eq3785 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3785
  have eq32163 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq196 y (σ x)
       have i₂ := eq31808
       grind)
    | exact superpose eq31808 eq196
    | exact resolve eq196 eq31808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32567 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq109 (σ y) (σ (M.op y y)) (σ x)
       have i₂ := eq32163
       grind)
    | exact superpose eq32163 eq109
    | exact resolve eq109 eq32163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq32163
  have eq32616 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32567
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq32567
    | exact resolve eq32567 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32567
  have eq32946 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (σ x) (σ y)
       have i₂ := eq32616
       grind)
    | exact superpose eq32616 eq23
    | exact resolve eq23 eq32616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32616
  have eq34118 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq32946 (σ y)
       have i₂ := eq31808
       grind)
    | exact superpose eq31808 eq32946
    | exact resolve eq32946 eq31808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31808 eq32946
  have eq34191 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq34118
  have eq34207 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34191
       have i₂ := eq195 y (σ x)
       grind)
    | exact superpose eq195 eq34191
    | exact resolve eq34191 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34191
  have eq34540 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq195 y X0
       have i₂ := eq34207
       grind)
    | exact superpose eq34207 eq195
    | exact resolve eq195 eq34207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36912 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq34540 (σ y)
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq34540
    | exact resolve eq34540 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34540
  have eq39975 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36912
       have i₂ := eq34207
       grind)
    | exact superpose eq34207 eq36912
    | exact resolve eq36912 eq34207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34207 eq36912
  have eq40036 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq39975
  have eq40054 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq40036
       have i₂ := eq98 (M.op x y)
       grind)
    | exact superpose eq98 eq40036
    | exact resolve eq40036 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40036
  have eq40445 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq40054
       grind)
    | exact superpose eq40054 eq10
    | exact resolve eq10 eq40054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40054
  have eq40669 : x = y ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq40445
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq40445
    | exact resolve eq40445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40445
  have eq41010 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40669
       grind)
    | exact superpose eq40669 eq16
    | exact resolve eq16 eq40669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40669
  have eq41011 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq41010
       have r₂ := eq98 x
       grind)
    | exact resolve eq41010 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41010
  have eq41416 : (M.op (M.op x y) (M.op x y)) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (M.op x y) (M.op x y))
       have i₂ := eq41011
       grind)
    | exact superpose eq41011 eq10
    | exact resolve eq10 eq41011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41433 : (τ (M.op (σ y) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq95 (M.op (M.op x y) (M.op x y))
       have i₂ := eq41011
       grind)
    | exact superpose eq41011 eq95
    | exact resolve eq95 eq41011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41651 : (M.op x y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq41433
       have i₂ := eq9 (M.op x y) x y (M.op x y)
       grind)
    | exact superpose eq9 eq41433
    | exact resolve eq41433 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41433
  have eq41664 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq41416
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq41416
    | exact resolve eq41416 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41416
  have eq41666 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq41651
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq41651
    | exact resolve eq41651 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq41651
  have eq95469 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3793 (M.op x x)
       have i₂ := eq23 x x y
       grind)
    | exact superpose eq23 eq3793
    | exact resolve eq3793 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3793
  have eq95595 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq195 x (σ y)
       have i₂ := eq95469
       grind)
    | exact superpose eq95469 eq195
    | exact resolve eq195 eq95469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq95708 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24 (σ x) (σ y) (σ (M.op x x))
       have i₂ := eq95595
       grind)
    | exact superpose eq95595 eq24
    | exact resolve eq24 eq95595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq95595
  have eq95833 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq95708
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq95708
    | exact resolve eq95708 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95708
  have eq95897 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) (σ y) X0
       have i₂ := eq95833
       grind)
    | exact superpose eq95833 eq23
    | exact resolve eq23 eq95833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95833
  have eq96567 : ∀ X0 : G, y = (M.op (M.op x x) (M.op x x)) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq41664
       have i₂ := eq95897 X0
       grind)
    | exact superpose eq95897 eq41664
    | (have j1 := eq95897 X0
       grind)
    | exact resolve eq41664 eq95897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41664 eq95897
  have eq96674 : ∀ X0 : G, x = y ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq96567 X0
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq96567 X0
       have i₂ := eq23 X0 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq23 eq96567
    | (have j0 := eq96567 X0
       grind)
    | exact resolve eq96567 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96567
  have eq97214 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq96674 X0
       grind)
    | exact superpose eq96674 eq16
    | (have j1 := eq96674 X0
       grind)
    | exact resolve eq16 eq96674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96674
  have eq97257 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq97214 X0
       grind)
    | (have r₁ := eq97214 X0
       have r₂ := eq98 x
       grind)
    | exact resolve eq97214 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97214
  have eq97271 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq97257 (σ x)
       have i₂ := eq95469
       grind)
    | exact superpose eq95469 eq97257
    | exact resolve eq97257 eq95469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95469
  have eq97288 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq197 x (M.op (σ y) x)
       have i₂ := eq97257 x
       grind)
    | exact superpose eq97257 eq197
    | exact resolve eq197 eq97257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq97257
  have eq97416 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97271
       have i₂ := eq196 x (σ y)
       grind)
    | exact superpose eq196 eq97271
    | exact resolve eq97271 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq97271
  have eq97436 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq97288
       grind)
    | exact superpose eq97288 eq16
    | exact resolve eq16 eq97288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97288
  have eq97768 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41011
       have i₂ := eq97416
       grind)
    | exact superpose eq97416 eq41011
    | exact resolve eq41011 eq97416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41011 eq97416
  have eq97906 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97768
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq97768
       have i₂ := eq23 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq23 eq97768
    | exact resolve eq97768 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq97768
  have eq97907 : (σ x) = (σ y) := by grind
  clear eq97906
  have eq97954 : (σ (M.op y y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq98 y
       have i₂ := eq97907
       grind)
    | exact superpose eq97907 eq98
    | exact resolve eq98 eq97907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97907
  have eq98355 : (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq97954
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq97954
    | exact resolve eq97954 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq97954
  have eq98371 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq98355
       have i₂ := eq41666
       grind)
    | exact superpose eq41666 eq98355
    | exact resolve eq98355 eq41666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41666 eq98355
  have eq98372 : False := by grind
  exact eq98372

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq63
    | exact resolve eq63 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq63
  have eq88 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq116 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X0) (τ X0)
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq19
    | exact resolve eq19 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq269 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op X2 (σ X1)) (M.op (σ X0) (σ X1))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq19 X0 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq19
    | (have j1 := eq88 X0 X1
       grind)
    | exact resolve eq19 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq291 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq292 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq296 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq65 X1
       grind)
    | exact superpose eq65 eq292
    | (have j0 := eq292 X0 X1
       grind)
    | exact resolve eq292 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq305 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq296 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq296
    | (have j0 := eq296 X0 X1
       grind)
    | exact resolve eq296 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq1319 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq305
    | (have j0 := eq305 X1 (τ X0)
       grind)
    | exact resolve eq305 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq1390 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1319 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq1319
    | (have j0 := eq1319 X0 X1
       grind)
    | exact resolve eq1319 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1401 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (k (τ X0) X1)) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1390 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq1390 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq1390 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390
  have eq1412 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1401 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq1401
    | (have j0 := eq1401 X0 X1
       grind)
    | exact resolve eq1401 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1401
  have eq1416 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1412 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq1412
    | (have j0 := eq1412 X0 X1
       grind)
    | exact resolve eq1412 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1528 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1416 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1416
    | exact resolve eq1416 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416
  have eq1670 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1528 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq1793 : ∀ X0 X1 : G, (τ X0) ≠ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) ∨ (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1670 (τ (M.op X0 X0)) (M.op X1 (τ X0))
       have i₂ := eq159 X0 X1
       grind)
    | exact superpose eq159 eq1670
    | exact resolve eq1670 eq159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq1670
  have eq1822 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1793 X0 X1
       have i₂ := eq116 (M.op X0 X0)
       grind)
    | exact superpose eq116 eq1793
    | (have j0 := eq1793 X0 X1
       grind)
    | exact resolve eq1793 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1793
  have eq1830 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1822 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq1822 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq1822
    | (have j0 := eq1822 X0 X1
       grind)
    | exact resolve eq1822 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822
  have eq1831 : ∀ X0 X1 : G, (τ X0) = (k (τ (M.op X0 X0)) (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1830 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830
  have eq1846 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (σ X0))) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1831 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1831
    | exact resolve eq1831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1831
  have eq1874 : ∀ X0 X1 : G, (k (τ (σ (M.op X0 X0))) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1846 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq1846
    | exact resolve eq1846 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq1846
  have eq1881 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1874 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1874
    | exact resolve eq1874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1874
  have eq1989 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1881 (M.op X0 X1) (M.op x X0)
       have i₂ := eq19 x X0 X1
       grind)
    | exact superpose eq19 eq1881
    | exact resolve eq1881 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1881
  have eq2473 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1989 (σ X1) (σ X0)
       have i₂ := eq269 X1 X0 (σ X1)
       grind)
    | exact superpose eq269 eq1989
    | (have j1 := eq269 X1 X0 x
       grind)
    | exact resolve eq1989 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq1989
  have eq2493 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2473 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq2473 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq2473 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq2506 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2493 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2493
    | (have j0 := eq2493 X0 X1
       grind)
    | exact resolve eq2493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2493
  have eq2507 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2506 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2506
  have eq2685 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2507 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2507
    | exact resolve eq2507 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2701 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2507 y x
       grind)
    | exact superpose eq2507 eq16
    | exact resolve eq16 eq2507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507
  have eq2980 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq2685 X0 (τ X1)
       grind)
    | exact superpose eq2685 eq17
    | exact resolve eq17 eq2685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2685
  have eq3046 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2980 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2980
    | exact resolve eq2980 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2980
  have eq3071 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3046 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3046
    | exact resolve eq3046 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3046
  have eq3202 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2701
       have i₂ := eq3071 x y
       grind)
    | exact superpose eq3071 eq2701
    | exact resolve eq2701 eq3071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701 eq3071
  have eq3203 : False := by grind
  exact eq3203

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (k X0 (k x y))) = (k (σ X0) (k (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (σ (k (k x y) X0)) = (k (k (σ x) (σ y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (k x y) X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10
    | exact resolve eq10 eq44
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
  have eq66 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
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
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq74 : (σ (k y (k x y))) = (k (σ y) (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq36 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq36
    | exact resolve eq36 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq70
    | (have j0 := eq70 (σ X0) (σ X1)
       grind)
    | exact resolve eq70 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq70
    | (have j0 := eq70 (σ y) (σ X0)
       grind)
    | exact resolve eq70 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq76
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq76 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq104 : ∀ X0 : G, (σ (k X0 (k y y))) = (k (σ X0) (k (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq10
    | exact resolve eq10 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq78 eq16
    | exact resolve eq16 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : (σ (k (M.op x y) (k y (M.op x y)))) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq78 eq37
    | exact resolve eq37 eq78
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
  have eq133 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq70 sF1 (σ X0)
       grind)
    | exact superpose eq70 eq37
    | (have j1 := eq70 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq145 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq70 (σ X0) sF2
       grind)
    | exact superpose eq70 eq39
    | (have j1 := eq70 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq155 : (k (σ (M.op x y)) (σ y)) = (σ (M.op y (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq131
       have i₂ := eq70 sF0 y
       grind)
    | exact superpose eq70 eq131
    | (have j1 := eq70 (M.op x y) y
       grind)
    | exact resolve eq131 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq131 eq16
    | exact resolve eq16 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq177 : (σ (k (k y (M.op x y)) y)) = (k (k (σ y) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq78 eq40
    | exact resolve eq40 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (k (k y y) (M.op x y))) = (k (k (σ y) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq41
    | exact resolve eq41 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq205 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq166
       have i₂ := eq70 sF1 sF1
       grind)
    | exact superpose eq70 eq166
    | (have j1 := eq70 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq166 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq50 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq207 eq14
    | exact resolve eq14 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq52 X2 X0 x
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ x = (k (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq265 eq13
    | exact resolve eq13 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq70 X1 (τ X0)
       grind)
    | exact superpose eq70 eq38
    | (have j1 := eq70 X1 (τ X0)
       grind)
    | exact resolve eq38 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 x) x) X0
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq12 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq657 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq658 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq657
    | (have j0 := eq657 X0 X1
       grind)
    | exact resolve eq657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq100 eq70
    | (have j0 := eq70 (σ y) (σ x)
       grind)
    | exact resolve eq70 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq908
    | exact resolve eq908 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq912 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq909
       have r₂ := eq27
       grind)
    | exact resolve eq909 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq914 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq912 eq256
    | exact resolve eq256 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq912 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq912
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq912
       grind)
    | exact resolve eq13 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq921 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq912 eq51
    | exact resolve eq51 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq929 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq917
  have eq987 : (τ (σ y)) = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq929 eq60
    | exact resolve eq60 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq989 : y = (k x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq987
    | exact resolve eq987 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1009 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq70 x y
       have i₂ := eq989
       grind)
    | exact superpose eq989 eq70
    | (have j0 := eq70 y x
       grind)
    | exact resolve eq70 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1010 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1009
  have eq1012 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1010
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1010
    | exact resolve eq1010 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq1041 : y = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq255 x
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq255
    | exact resolve eq255 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1042 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq265 y
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq265
    | exact resolve eq265 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : y ≠ y ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq1012
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1012
       grind)
    | exact resolve eq13 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1047 : y = (M.op (M.op (M.op x y) y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq50 y x
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq50
    | exact resolve eq50 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1051 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53 y x x
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq53
    | exact resolve eq53 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1056 : y = (k x y) ∨ x = (M.op x y) := by grind
  clear eq1044
  have eq1080 : x ≠ y ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1042 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq1042
       grind)
    | exact resolve eq13 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1093 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1056
       grind)
    | exact superpose eq1056 eq44
    | exact resolve eq44 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1056
  have eq1095 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1093
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1093
    | exact resolve eq1093 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1093
  have eq1147 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1041 eq1047
    | exact resolve eq1047 eq1041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041 eq1047
  have eq1167 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1147
  have eq1171 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1167
       grind)
    | exact superpose eq1167 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1167
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1167
       grind)
    | exact resolve eq13 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1183 : y = (k y y) ∨ x = (M.op x y) := by grind
  clear eq1171
  have eq1185 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq1183
       grind)
    | exact superpose eq1183 eq77
    | exact resolve eq77 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1189 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1185
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1185
    | exact resolve eq1185 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1934 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq914 eq921
    | exact resolve eq921 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq921
  have eq1958 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1934
  have eq1965 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1958 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1958
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1958
       grind)
    | exact resolve eq13 eq1958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq1980 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq1965
  have eq2024 : (τ (σ y)) = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1980 eq106
    | exact resolve eq106 eq1980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2028 : y = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq2024
    | exact resolve eq2024 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024
  have eq2031 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq70 y y
       have i₂ := eq2028
       grind)
    | exact superpose eq2028 eq70
    | (have j0 := eq70 y y
       grind)
    | exact resolve eq70 eq2028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2028
  have eq2032 : y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq2031
  have eq2670 : ∀ X0 X1 : G, (σ (k y X0)) = (M.op (M.op X1 (σ (k y X0))) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq86 eq267
    | (have j1 := eq86 X0
       grind)
    | exact resolve eq267 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq267
  have eq2716 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (k (M.op x y) X0)) (M.op (σ (M.op x y)) X1)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq133 eq52
    | (have j1 := eq133 X0
       grind)
    | exact resolve eq52 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq3282 : (σ (σ y)) ≠ (σ (σ y)) ∨ (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1189 eq656
    | (have j0 := eq656 (σ y)
       grind)
    | exact resolve eq656 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3288 : (σ (σ y)) = (M.op (σ (σ y)) (σ (σ y))) ∨ x = (M.op x y) := by grind
  clear eq3282
  have eq3305 : (σ (σ y)) ≠ (σ (σ y)) ∨ (σ (σ y)) = (k (σ (σ y)) (σ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3288 eq13
    | (have r₁ := eq13 (σ (σ y)) (σ (σ y))
       have r₂ := eq3288
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3288
       grind)
    | exact resolve eq13 eq3288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3288
  have eq3320 : (σ (σ y)) = (k (σ (σ y)) (σ (σ y))) ∨ x = (M.op x y) := by grind
  clear eq3305
  have eq3321 : (σ (σ y)) = (σ (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3320
       have i₂ := eq10 sF3 sF3
       grind)
    | exact superpose eq10 eq3320
    | exact resolve eq3320 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320
  have eq3343 : ∀ X0 : G, (k (τ X0) (k (σ y) (σ y))) = (τ (k X0 (σ (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3321 eq352
    | exact resolve eq352 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3348 : ∀ X0 : G, (k (k (σ y) (σ y)) (τ X0)) = (τ (k (σ (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3321 eq377
    | exact resolve eq377 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq3350 : ∀ X0 : G, (k (k (σ y) (σ y)) (τ X0)) = (k (σ y) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3348 x
       have i₂ := eq377 sF3 x
       grind)
    | exact superpose eq377 eq3348
    | exact resolve eq3348 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348
  have eq3355 : ∀ X0 : G, (k (τ X0) (k (σ y) (σ y))) = (k (τ X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3343 X0
       have i₂ := eq352 X0 sF3
       grind)
    | exact superpose eq352 eq3343
    | exact resolve eq3343 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3343
  have eq3425 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X1 (σ x)) (σ (k X0 x))) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq145 eq52
    | (have j1 := eq145 X0
       grind)
    | exact resolve eq52 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq3766 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq372 (σ X0) X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq372
    | exact resolve eq372 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq3817 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3766 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq3766
    | (have j0 := eq3766 X0 X1
       grind)
    | exact resolve eq3766 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3766
  have eq4489 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ y) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3350 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3350
    | exact resolve eq3350 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq4782 : ∀ X0 : G, (k (τ (k (σ y) (σ y))) X0) = (τ (k (σ y) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4489 eq352
    | exact resolve eq352 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4489
  have eq4797 : ∀ X0 : G, (k (τ (k (σ y) (σ y))) X0) = (k (τ (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4782 x
       have i₂ := eq352 sF3 x
       grind)
    | exact superpose eq352 eq4782
    | exact resolve eq4782 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4782
  have eq4800 : ∀ X0 : G, (k y X0) = (k (τ (k (σ y) (σ y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq4797
    | exact resolve eq4797 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4797
  have eq4803 : ∀ X0 : G, (k y X0) = (k (k y y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106 eq4800
    | exact resolve eq4800 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4800
  have eq5053 : ∀ X0 : G, (k (τ (k y y)) X0) = (τ (k y (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq352 (k y y) X0
       have i₂ := eq4803 (σ X0)
       grind)
    | exact superpose eq4803 eq352
    | exact resolve eq352 eq4803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq5068 : ∀ X0 : G, (k (τ (k y y)) X0) = (k (τ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5053 X0
       have i₂ := eq352 y X0
       grind)
    | exact superpose eq352 eq5053
    | exact resolve eq5053 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq5053
  have eq5093 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3355 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3355
    | exact resolve eq3355 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq5160 : ∀ X0 : G, (k X0 (τ (k (σ y) (σ y)))) = (τ (k (σ X0) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5093 eq377
    | exact resolve eq377 eq5093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5093
  have eq5165 : ∀ X0 : G, (k X0 (τ (k (σ y) (σ y)))) = (k X0 (τ (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5160 X0
       have i₂ := eq377 X0 sF3
       grind)
    | exact superpose eq377 eq5160
    | exact resolve eq5160 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq5160
  have eq5175 : ∀ X0 : G, (k X0 y) = (k X0 (τ (k (σ y) (σ y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq5165
    | exact resolve eq5165 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5165
  have eq5178 : ∀ X0 : G, (k X0 y) = (k X0 (k y y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106 eq5175
    | exact resolve eq5175 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5175
  have eq6800 : (σ (τ (k y y))) ≠ (σ (k (τ y) (τ (k y y)))) ∨ (σ (τ (k y y))) = (M.op (σ (τ (k y y))) (σ (τ (k y y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq656 (τ (k y y))
       have i₂ := eq5068 (τ (k y y))
       grind)
    | exact superpose eq5068 eq656
    | (have j0 := eq656 (τ (k y y))
       grind)
    | exact resolve eq656 eq5068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq5068
  have eq6871 : (σ (τ (k y y))) ≠ (k y (σ (τ (k y y)))) ∨ (σ (τ (k y y))) = (M.op (σ (τ (k y y))) (σ (τ (k y y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6800
       have i₂ := eq34 y (τ (k y y))
       grind)
    | exact superpose eq34 eq6800
    | exact resolve eq6800 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq6800
  have eq6890 : (k y y) ≠ (k y (k y y)) ∨ (σ (τ (k y y))) = (M.op (σ (τ (k y y))) (σ (τ (k y y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6871
       have i₂ := eq15 (k y y)
       grind)
    | exact superpose eq15 eq6871
    | exact resolve eq6871 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6871
  have eq6900 : (σ (τ (k y y))) = (M.op (σ (τ (k y y))) (σ (τ (k y y)))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6890
       have r₂ := eq5178 y
       grind)
    | exact resolve eq6890 eq5178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5178 eq6890
  have eq6902 : (k y y) = (M.op (k y y) (k y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6900
       have i₂ := eq15 (k y y)
       grind)
    | exact superpose eq15 eq6900
    | exact resolve eq6900 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6900
  have eq7552 : (k y y) ≠ (k y y) ∨ (k y y) = (k (k y y) (k y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (k y y) (k y y)
       have i₂ := eq6902
       grind)
    | exact superpose eq6902 eq13
    | (have r₁ := eq13 (k y y) (k y y)
       have r₂ := eq6902
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6902
       grind)
    | exact resolve eq13 eq6902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7566 : ∀ X0 : G, (k y y) ≠ (k y y) ∨ (k y y) = (k (M.op (k y y) X0) (k y y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq438 (k y y) (k y y) x
       have i₂ := eq6902
       grind)
    | exact superpose eq6902 eq438
    | (have r₁ := eq438 (k y y) (k y y) x
       have r₂ := eq6902
       grind)
    | (have r₁ := eq438 x y x
       have r₂ := eq6902
       grind)
    | exact resolve eq438 eq6902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq6902
  have eq7567 : ∀ X0 : G, (k y y) = (k (M.op (k y y) X0) (k y y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7566
  have eq7569 : (k y y) = (k (k y y) (k y y)) ∨ x = (M.op x y) := by grind
  clear eq7552
  have eq7996 : (σ (k y y)) ≠ (σ (k y y)) ∨ (σ (k y y)) = (M.op (σ (k y y)) (σ (k y y))) ∨ (σ (k y y)) = (M.op (σ (k y y)) (σ (k y y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq658 (k y y) (k y y)
       have i₂ := eq7569
       grind)
    | exact superpose eq7569 eq658
    | (have j0 := eq658 (k y y) (k y y)
       grind)
    | exact resolve eq658 eq7569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7569
  have eq7997 : (σ (k y y)) ≠ (σ (k y y)) ∨ (σ (k y y)) = (M.op (σ (k y y)) (σ (k y y))) ∨ x = (M.op x y) := by grind
  clear eq7996
  have eq7998 : (σ (k y y)) = (M.op (σ (k y y)) (σ (k y y))) ∨ x = (M.op x y) := by grind
  clear eq7997
  have eq8007 : (k (σ y) (σ y)) = (M.op (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7998
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq7998
    | exact resolve eq7998 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7998
  have eq8022 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8007 eq13
    | (have r₁ := eq13 (k (σ y) (σ y)) (k (σ y) (σ y))
       have r₂ := eq8007
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8007
       grind)
    | exact resolve eq13 eq8007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8007
  have eq8041 : (k (σ y) (σ y)) = (k (k (σ y) (σ y)) (k (σ y) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq8022
  have eq24192 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (k x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1095 eq58
    | exact resolve eq58 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq24231 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (k x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40 eq24192
    | exact resolve eq24192 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24192
  have eq24315 : ∀ X0 : G, (k X0 (k x y)) = (τ (σ (k X0 y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 (k X0 (k x y))
       have i₂ := eq24231 X0
       grind)
    | exact superpose eq24231 eq16
    | exact resolve eq16 eq24231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24393 : ∀ X0 : G, (k X0 y) = (k X0 (k x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24315 X0
       have i₂ := eq16 (k X0 y)
       grind)
    | exact superpose eq16 eq24315
    | exact resolve eq24315 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24315
  have eq24439 : ∀ X0 : G, (k X0 y) = (k X0 (M.op y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24393 X0
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq24393
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq24393 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24571 : ∀ X0 : G, x = (M.op x y) ∨ (k X0 y) = (k X0 (M.op y x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24439 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24439
    | (have j0 := eq24439 X0
       grind)
    | exact resolve eq24439 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24439
  have eq24572 : ∀ X0 : G, (k X0 y) = (k X0 (M.op y x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq24571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24571
  have eq24736 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (k x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1095 eq59
    | exact resolve eq59 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1095
  have eq24956 : ∀ X0 : G, (σ (k y X0)) = (σ (k (k x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36 eq24736
    | exact resolve eq24736 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq24736
  have eq26429 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op y x) X0)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq24956 X0
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq24956
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq24956 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26467 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (k x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (k x y)
       have i₂ := eq24956 (τ X0)
       grind)
    | exact superpose eq24956 eq38
    | exact resolve eq38 eq24956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26474 : ∀ X0 : G, (k (k x y) X0) = (τ (σ (k y X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 (k (k x y) X0)
       have i₂ := eq24956 X0
       grind)
    | exact superpose eq24956 eq16
    | exact resolve eq16 eq24956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24956
  have eq26570 : ∀ X0 : G, (k y X0) = (k (k x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26474 X0
       have i₂ := eq16 (k y X0)
       grind)
    | exact superpose eq16 eq26474
    | exact resolve eq26474 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26474
  have eq26574 : ∀ X0 : G, (σ (k y (τ X0))) = (k (k (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26467 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq26467
    | exact resolve eq26467 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26467
  have eq26597 : ∀ X0 : G, x = (M.op x y) ∨ (σ (k y X0)) = (σ (k (M.op y x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26429 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26429
    | (have j0 := eq26429 X0
       grind)
    | exact resolve eq26429 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26429
  have eq26598 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op y x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq26597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26597
  have eq26600 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26574 X0
       have i₂ := eq38 X0 y
       grind)
    | exact superpose eq38 eq26574
    | exact resolve eq26574 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq26574
  have eq26611 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26600 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq26600
    | (have j0 := eq26600 X0
       grind)
    | exact resolve eq26600 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26600
  have eq26620 : ∀ X0 : G, (k y X0) = (k (M.op y x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26570 X0
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq26570
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq26570 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26570
  have eq26771 : ∀ X0 : G, x = (M.op x y) ∨ (k y X0) = (k (M.op y x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq26620 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq26620
    | (have j0 := eq26620 X0
       grind)
    | exact resolve eq26620 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26620
  have eq26772 : ∀ X0 : G, (k y X0) = (k (M.op y x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq26771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26771
  have eq27071 : (k y (k x y)) = (k (M.op y x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24393 (M.op y x)
       have i₂ := eq26772 (k x y)
       grind)
    | exact superpose eq26772 eq24393
    | exact resolve eq24393 eq26772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24393 eq26772
  have eq27121 : (k y (k x y)) = (k (M.op y x) y) ∨ x = (M.op x y) := by grind
  clear eq27071
  have eq27937 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (k y y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1189 eq104
    | exact resolve eq104 eq1189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1189
  have eq28003 : ∀ X0 : G, (σ (k X0 y)) = (σ (k X0 (k y y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40 eq27937
    | exact resolve eq27937 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq27937
  have eq28722 : (σ (k y (k x y))) = (σ (k (M.op y x) y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24231 (M.op y x)
       have i₂ := eq26598 (k x y)
       grind)
    | exact superpose eq26598 eq24231
    | exact resolve eq24231 eq26598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24231 eq26598
  have eq28777 : (σ (k y (k x y))) = (σ (k (M.op y x) y)) ∨ x = (M.op x y) := by grind
  clear eq28722
  have eq28837 : (k (σ y) (k (σ x) (σ y))) = (σ (k (M.op y x) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28777
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq28777
    | exact resolve eq28777 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq28777
  have eq30782 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1042 eq155
    | exact resolve eq155 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq30840 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq30782
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30782
    | exact resolve eq30782 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30782
  have eq30842 : (τ (σ x)) = (k (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30840 eq158
    | exact resolve eq158 eq30840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30840
  have eq30850 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq30842
    | exact resolve eq30842 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30842
  have eq30865 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30850 eq216
    | exact resolve eq216 eq30850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq30873 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30850 eq13
    | (have r₁ := eq13 y (M.op x y)
       have r₂ := eq30850
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq30850
       grind)
    | exact resolve eq13 eq30850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30878 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30850 eq52
    | exact resolve eq52 eq30850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq30850
  have eq30896 : (M.op x y) = (k y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq30873
  have eq31186 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30896 eq78
    | exact resolve eq78 eq30896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30896
  have eq31219 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq31186
    | exact resolve eq31186 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31186
  have eq32247 : ∀ X0 : G, (σ (k y y)) = (σ (k (M.op (k y y) X0) y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28003 (M.op (k y y) X0)
       have i₂ := eq7567 X0
       grind)
    | exact superpose eq7567 eq28003
    | exact resolve eq28003 eq7567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7567 eq28003
  have eq32384 : ∀ X0 : G, (σ (k y y)) = (σ (k (M.op (k y y) X0) y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq32247 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32247
  have eq32453 : ∀ X0 : G, (k (σ y) (σ y)) = (σ (k (M.op (k y y) X0) y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq32384 X0
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq32384
    | exact resolve eq32384 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32384
  have eq49982 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30865 eq30878
    | exact resolve eq30878 eq30865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30865 eq30878
  have eq50018 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq49982
  have eq50062 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq50018 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq50018
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq50018
       grind)
    | exact resolve eq13 eq50018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50018
  have eq50087 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq50062
  have eq51496 : (τ (k (σ y) (k (σ x) (σ y)))) = (k (M.op y x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16 (k (M.op y x) y)
       have i₂ := eq28837
       grind)
    | exact superpose eq28837 eq16
    | exact resolve eq16 eq28837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28837
  have eq62031 : ∀ X0 : G, (k (σ y) (σ y)) = (σ (k (M.op y X0) y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq32453 X0
       have i₂ := eq1183
       grind)
    | exact superpose eq1183 eq32453
    | exact resolve eq32453 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183 eq32453
  have eq62128 : ∀ X0 : G, (k (σ y) (σ y)) = (σ (k (M.op y X0) y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq62031 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62031
  have eq62152 : (σ (k x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1042 eq62128
    | exact resolve eq62128 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62128
  have eq62264 : (σ (k x y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq62152
  have eq62281 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62264
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq62264
    | exact resolve eq62264 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq62264
  have eq62352 : (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62281 eq8041
    | exact resolve eq8041 eq62281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8041 eq62281
  have eq62440 : (k (σ x) (σ y)) = (k (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq62352
  have eq63794 : (k (σ x) (σ y)) = (k (σ y) (k (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62440 eq26611
    | exact resolve eq26611 eq62440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26611 eq62440
  have eq63810 : (k (σ x) (σ y)) = (k (σ y) (k (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq63794
  have eq63840 : (τ (k (σ x) (σ y))) = (k (M.op y x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63810 eq51496
    | exact resolve eq51496 eq63810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51496 eq63810
  have eq63860 : (τ (k (σ x) (σ y))) = (k (M.op y x) y) ∨ x = (M.op x y) := by grind
  clear eq63840
  have eq63873 : (k x y) = (k (M.op y x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60 eq63860
    | exact resolve eq63860 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq63860
  have eq64219 : (k x y) = (k y (k x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq27121
       have i₂ := eq63873
       grind)
    | exact superpose eq63873 eq27121
    | exact resolve eq27121 eq63873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27121 eq63873
  have eq64253 : (k x y) = (k y (k x y)) ∨ x = (M.op x y) := by grind
  clear eq64219
  have eq64689 : (M.op y x) = (k y (M.op y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64253
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq64253
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq64253 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64253
  have eq64729 : x = (M.op x y) ∨ (M.op y x) = (k y (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq64689
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq64689
    | exact resolve eq64689 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64689
  have eq64730 : (M.op y x) = (k y (M.op y x)) ∨ x = (M.op x y) := by grind
  clear eq64729
  have eq64926 : (k y y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24572 y
       have i₂ := eq64730
       grind)
    | exact superpose eq64730 eq24572
    | exact resolve eq24572 eq64730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24572 eq64730
  have eq64937 : (k y y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq64926
  have eq64971 : (k (k (σ y) (σ y)) (σ (M.op x y))) = (σ (k (M.op y x) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq195
       have i₂ := eq64937
       grind)
    | exact superpose eq64937 eq195
    | exact resolve eq195 eq64937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq79360 : (k (k (σ y) (σ y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op y x))) ∨ (M.op y x) = (M.op (M.op y x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64971 eq3817
    | (have j0 := eq3817 (M.op x y) (M.op y x)
       grind)
    | exact resolve eq3817 eq64971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817
  have eq79363 : (τ (k (k (σ y) (σ y)) (σ (M.op x y)))) = (k (M.op y x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64971 eq16
    | exact resolve eq16 eq64971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64971
  have eq79449 : (σ y) = (k (k (σ y) (σ y)) (σ (M.op x y))) ∨ (M.op y x) = (M.op (M.op y x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq255 eq79360
    | exact resolve eq79360 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq79360
  have eq79465 : (σ y) = (k (k (σ y) (σ y)) (σ (M.op x y))) ∨ (M.op y x) = (M.op (M.op y x) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79449
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq79449
    | exact resolve eq79449 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79449
  have eq79475 : (σ y) = (k (k (σ y) (σ y)) (σ (M.op x y))) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq265 eq79465
    | exact resolve eq79465 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq79465
  have eq86335 : (τ (σ y)) = (k (M.op y x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79475 eq79363
    | exact resolve eq79363 eq79475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79363 eq79475
  have eq86368 : (τ (σ y)) = (k (M.op y x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq86335
  have eq86375 : y = (k (M.op y x) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq86368
    | exact resolve eq86368 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86368
  have eq93674 : y = (k y (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq86375
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq86375
    | exact resolve eq86375 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012 eq86375
  have eq93704 : y = (k y (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq93674
  have eq93733 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93704 eq78
    | exact resolve eq78 eq93704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq93736 : (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) = (σ (k (M.op x y) y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93704 eq129
    | exact resolve eq129 eq93704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq93738 : (σ (k y y)) = (k (k (σ y) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq93704 eq177
    | exact resolve eq177 eq93704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq93704
  have eq93773 : (k (σ y) (σ y)) = (k (k (σ y) (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq93738
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq93738
    | exact resolve eq93738 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq93738
  have eq93775 : (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq131 eq93736
    | exact resolve eq93736 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93736
  have eq93778 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq93733
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq93733
    | exact resolve eq93733 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93733
  have eq94264 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq93778
       have i₂ := eq70 sF3 sF1
       grind)
    | exact superpose eq70 eq93778
    | (have j1 := eq70 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq93778 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq97159 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31219 eq93773
    | exact resolve eq93773 eq31219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93773
  have eq97170 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (k (M.op x y) y) := by grind
  clear eq97159
  have eq97172 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq97170
       have r₂ := eq1080
       grind)
    | exact resolve eq97170 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97170
  have eq97186 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31219 eq93775
    | exact resolve eq93775 eq31219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31219 eq93775
  have eq97197 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (k (M.op x y) y) := by grind
  clear eq97186
  have eq97198 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have r₁ := eq97197
       have r₂ := eq1080
       grind)
    | exact resolve eq97197 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97197
  have eq98370 : (k y y) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq97172 eq106
    | exact resolve eq106 eq97172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq97172
  have eq98633 : (k y y) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq158 eq98370
    | exact resolve eq98370 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98370
  have eq99793 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq97198 eq158
    | exact resolve eq158 eq97198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq97198
  have eq99858 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq166 eq99793
    | exact resolve eq99793 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq99793
  have eq104340 : (M.op x y) = (k (M.op x y) y) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq99858 eq50087
    | exact resolve eq50087 eq99858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50087 eq99858
  have eq104358 : (M.op x y) = (k (M.op x y) y) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq104340
  have eq104418 : (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104358 eq98633
    | exact resolve eq98633 eq104358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98633 eq104358
  have eq104436 : (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by grind
  clear eq104418
  have eq105056 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have i₁ := eq64937
       have i₂ := eq104436
       grind)
    | exact superpose eq104436 eq64937
    | exact resolve eq64937 eq104436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64937 eq104436
  have eq105091 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by grind
  clear eq105056
  have eq105871 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | (have i₁ := eq1051 x
       have i₂ := eq105091
       grind)
    | exact superpose eq105091 eq1051
    | exact resolve eq1051 eq105091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq105091
  have eq105909 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by grind
  clear eq105871
  have eq107637 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq105909 eq1042
    | exact resolve eq1042 eq105909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq105909
  have eq107681 : x = y ∨ x = (M.op x y) ∨ x = (k (M.op x y) y) := by grind
  clear eq107637
  have eq107685 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq107681
       have r₂ := eq1080
       grind)
    | exact resolve eq107681 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq107681
  have eq108167 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107685 eq131
    | exact resolve eq131 eq107685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq108181 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq107685 eq2716
    | (have j0 := eq2716 y x
       grind)
    | exact resolve eq2716 eq107685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2716 eq107685
  have eq108200 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq108181 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108181
    | (have j0 := eq108181 X0
       grind)
    | exact resolve eq108181 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108181
  have eq108214 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108167
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq108167
    | exact resolve eq108167 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108167
  have eq108221 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq108200 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq108200
    | (have j0 := eq108200 X0
       grind)
    | exact resolve eq108200 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108200
  have eq234316 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq3425 eq2670
    | (have j0 := eq2670 x x
       have j1 := eq3425 y x
       grind)
    | exact resolve eq2670 eq3425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2670 eq3425
  have eq234383 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq234316
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq234316
    | exact resolve eq234316 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234316
  have eq234472 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq234383
    | exact resolve eq234383 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234383
  have eq234505 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq234472
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq234472
    | exact resolve eq234472 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234472
  have eq234517 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq234505
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq234505
    | exact resolve eq234505 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234505
  have eq234518 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq234517
  have eq2106635 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq94264 eq13
    | (have r₁ := eq13 (σ (M.op x y)) (σ y)
       have r₂ := eq94264
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq94264
       grind)
    | exact resolve eq13 eq94264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94264
  have eq2106675 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq2106635
  have eq2140675 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2106675 eq108214
    | exact resolve eq108214 eq2106675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2106675
  have eq2140829 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2140675
  have eq2141623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2140829 eq108221
    | exact resolve eq108221 eq2140829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108221 eq2140829
  have eq2141704 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2141623
  have eq2141708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq2141704
    | exact resolve eq2141704 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141704
  have eq2141710 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq2141708
       have r₂ := eq27
       grind)
    | exact resolve eq2141708 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141708
  have eq2141712 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2141710 eq29
    | exact resolve eq29 eq2141710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141710
  have eq2144734 : x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28 eq2141712
    | exact resolve eq2141712 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2141712
  have eq2144735 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2144734
  have eq2145469 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2144735 eq93778
    | exact resolve eq93778 eq2144735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93778
  have eq2145491 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2144735 eq108214
    | exact resolve eq108214 eq2144735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108214 eq2144735
  have eq2147193 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2145491
  have eq2147215 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2145469
  have eq2150787 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2147215 eq2147193
    | exact resolve eq2147193 eq2147215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2147193 eq2147215
  have eq2150858 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2150787
  have eq2150878 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2150858 eq28
    | exact resolve eq28 eq2150858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150858
  have eq2152823 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq2150878
    | exact resolve eq2150878 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150878
  have eq2152824 : x = (M.op x y) ∨ x = y := by grind
  clear eq2152823
  have eq2153536 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2152824 eq20
    | exact resolve eq20 eq2152824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2153540 : x ≠ x ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq2152824 eq66
    | (have r₁ := eq66
       have r₂ := eq2152824
       grind)
    | exact resolve eq66 eq2152824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2153588 : x = (M.op (M.op x x) x) ∨ x = y := by
    first
    | exact superpose eq2152824 eq207
    | exact resolve eq207 eq2152824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq2153994 : x = (k y x) ∨ x = y := by grind
  clear eq2153540
  have eq2154195 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2153536
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2153536
    | exact resolve eq2153536 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153536
  have eq2154213 : (k y x) = (τ (k (σ y) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq2154195 eq83
    | exact resolve eq83 eq2154195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2155328 : (k y x) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq112 eq2154213
    | exact resolve eq2154213 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154213
  have eq2155350 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq2153994
       grind)
    | exact superpose eq2153994 eq76
    | exact resolve eq76 eq2153994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153994
  have eq2155595 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2155350
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2155350
    | exact resolve eq2155350 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155350
  have eq2156591 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2154195 eq2155595
    | exact resolve eq2155595 eq2154195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154195 eq2155595
  have eq2156710 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = y := by grind
  clear eq2156591
  have eq2156741 : (τ (σ (M.op x y))) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2156710 eq112
    | exact resolve eq112 eq2156710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq2156710
  have eq2156854 : (M.op x y) = (k y (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq2156741
    | exact resolve eq2156741 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2156741
  have eq2158017 : x ≠ x ∨ x = (k (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq302 (M.op x x)
       have i₂ := eq2153588
       grind)
    | exact superpose eq2153588 eq302
    | (have r₁ := eq302 (M.op x x)
       have r₂ := eq2153588
       grind)
    | exact resolve eq302 eq2153588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq2153588
  have eq2158061 : x = (k (M.op x y) x) ∨ x = y := by grind
  clear eq2158017
  have eq2158869 : x = (k x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2152824 eq2158061
    | exact resolve eq2158061 eq2152824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2152824 eq2158061
  have eq2158986 : x = (k x x) ∨ x = y := by grind
  clear eq2158869
  have eq2160139 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq658 x x
       have i₂ := eq2158986
       grind)
    | exact superpose eq2158986 eq658
    | (have j0 := eq658 x x
       grind)
    | exact resolve eq658 eq2158986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq2158986
  have eq2160183 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq2160139
  have eq2160184 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq2160183
  have eq2160227 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2160184
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2160184
    | exact resolve eq2160184 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160184
  have eq2161277 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2160227 eq51
    | exact resolve eq51 eq2160227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2160227
  have eq2182185 : (M.op x y) = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2155328 eq2156854
    | exact resolve eq2156854 eq2155328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155328 eq2156854
  have eq2182270 : (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq2182185
  have eq2183361 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq76
       have i₂ := eq2182270
       grind)
    | exact superpose eq2182270 eq76
    | exact resolve eq76 eq2182270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq2182270
  have eq2183608 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq2183361
    | exact resolve eq2183361 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183361
  have eq2183914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2183608 eq234518
    | exact resolve eq234518 eq2183608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234518 eq2183608
  have eq2183987 : (σ y) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq2183914
       have r₂ := eq27
       grind)
    | exact resolve eq2183914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183914
  have eq2184861 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq2183987 eq266
    | exact resolve eq266 eq2183987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq2185815 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2184861 eq256
    | exact resolve eq256 eq2184861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq2184861
  have eq2215759 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2185815 eq2161277
    | exact resolve eq2161277 eq2185815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161277 eq2185815
  have eq2215829 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by grind
  clear eq2215759
  have eq2215947 : (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2215829 eq2183987
    | exact resolve eq2183987 eq2215829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183987 eq2215829
  have eq2216069 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2215947
  have eq2216091 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2216069 eq29
    | exact resolve eq29 eq2216069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2216069
  have eq2217870 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq2216091
    | exact resolve eq2216091 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2216091
  have eq2217871 : x = y := by grind
  clear eq2217870
  have eq2218604 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2217871
       grind)
    | exact superpose eq2217871 eq18
    | exact resolve eq18 eq2217871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2218605 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2217871
       grind)
    | exact superpose eq2217871 eq24
    | exact resolve eq24 eq2217871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2218727 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2032
       have i₂ := eq2217871
       grind)
    | exact superpose eq2217871 eq2032
    | exact resolve eq2032 eq2217871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032
  have eq2220528 : x = (M.op x x) := by grind
  clear eq2218727
  have eq2220809 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2218605
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2218605
    | exact resolve eq2218605 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218605
  have eq2220811 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2220809 eq26
    | exact resolve eq26 eq2220809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2220809
  have eq2223537 : x = (M.op x y) := by
    first
    | (have i₁ := eq2220528
       have i₂ := eq2218604
       grind)
    | exact superpose eq2218604 eq2220528
    | exact resolve eq2220528 eq2218604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218604 eq2220528
  have eq2223539 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2223537 eq20
    | exact resolve eq20 eq2223537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2223543 : x ≠ x ∨ x = (k y x) := by
    first
    | exact superpose eq2223537 eq66
    | (have r₁ := eq66
       have r₂ := eq2223537
       grind)
    | exact resolve eq66 eq2223537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq2224058 : x = (k y x) := by grind
  clear eq2223543
  have eq2224357 : x = (k x x) := by
    first
    | (have i₁ := eq2224058
       have i₂ := eq2217871
       grind)
    | exact superpose eq2217871 eq2224058
    | exact resolve eq2224058 eq2217871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217871 eq2224058
  have eq2224360 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2223539
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2223539
    | exact resolve eq2223539 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223539
  have eq2226324 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2224360 eq2220811
    | exact resolve eq2220811 eq2224360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220811
  have eq2227104 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2226324 eq205
    | exact resolve eq205 eq2226324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq2226324
  have eq2227200 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq2227104
       have r₂ := eq27
       grind)
    | exact resolve eq2227104 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227104
  have eq2227216 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2223537 eq2227200
    | exact resolve eq2227200 eq2223537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223537 eq2227200
  have eq2227229 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2227216
       have i₂ := eq2224357
       grind)
    | exact superpose eq2224357 eq2227216
    | exact resolve eq2227216 eq2224357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224357 eq2227216
  have eq2227257 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2227229 eq15
    | exact resolve eq15 eq2227229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227229
  have eq2228277 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2227257
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2227257
    | exact resolve eq2227257 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2227257
  have eq2228520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2224360 eq2228277
    | exact resolve eq2228277 eq2224360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2224360 eq2228277
  have eq2228708 : False := by grind
  exact eq2228708

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq61 X3 X0 x
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq346 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq348 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq349 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq348 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq350 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq347 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq347 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq347 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq371 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq350 (σ X0)
       grind)
    | exact superpose eq350 eq15
    | exact resolve eq15 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq350 X0
       grind)
    | exact superpose eq350 eq371
    | exact resolve eq371 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq438 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq61
    | exact resolve eq61 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X1
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq61
    | exact resolve eq61 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0) x
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq62
    | exact resolve eq62 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq485 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq349 (σ X1) (σ X0)
       grind)
    | exact superpose eq349 eq15
    | (have j1 := eq349 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq349 X1 (τ X0)
       grind)
    | exact superpose eq349 eq17
    | (have j1 := eq349 X1 (τ X0)
       grind)
    | exact resolve eq17 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq349
  have eq1062 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq493 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq493
    | exact resolve eq493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq1122 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1062 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1062
    | (have j0 := eq1062 X0 X1
       grind)
    | exact resolve eq1062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1872 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq485 x y
       grind)
    | exact superpose eq485 eq16
    | (have j1 := eq485 x y
       grind)
    | exact resolve eq16 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1917 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq485 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq2061 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1872
       have i₂ := eq1122 x y
       grind)
    | exact superpose eq1122 eq1872
    | (have j1 := eq1122 (σ x) (σ y)
       grind)
    | (have r₁ := eq1872
       have r₂ := eq1122 x y
       grind)
    | exact resolve eq1872 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2062 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2061
  have eq2068 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2062
       grind)
    | exact superpose eq2062 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2062
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2062
       grind)
    | exact resolve eq13 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2071 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2062
       grind)
    | exact superpose eq2062 eq61
    | exact resolve eq61 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2080 : y = (k x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2068
  have eq2110 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2071 (M.op y x)
       have i₂ := eq2071 x
       grind)
    | exact superpose eq2071 eq2071
    | exact resolve eq2071 eq2071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071
  have eq2127 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2110
  have eq2132 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq438 y (σ x)
       have i₂ := eq2127
       grind)
    | exact superpose eq2127 eq438
    | exact resolve eq438 eq2127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq2139 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq2127
       grind)
    | exact superpose eq2127 eq61
    | exact resolve eq61 eq2127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2299 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2139 (σ (M.op y y))
       have i₂ := eq2132
       grind)
    | exact superpose eq2132 eq2139
    | exact resolve eq2139 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132 eq2139
  have eq2319 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2299
  have eq2322 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2319
       have i₂ := eq390 y
       grind)
    | exact superpose eq390 eq2319
    | exact resolve eq2319 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319
  have eq2355 : ∀ X0 X1 : G, (σ y) = (σ (M.op y y)) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq69 y X1 x y
       have i₂ := eq2322
       grind)
    | exact superpose eq2322 eq69
    | exact resolve eq69 eq2322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq2322
  have eq2547 : ∀ X0 X1 : G, (τ (σ y)) = (M.op y y) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq2355 X0 X1
       grind)
    | exact superpose eq2355 eq10
    | (have j1 := eq2355 X0 X1
       grind)
    | exact resolve eq10 eq2355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355
  have eq2606 : ∀ X0 X1 : G, y = (M.op y y) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq2547 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2547
    | (have j0 := eq2547 X0 X1
       grind)
    | exact resolve eq2547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2547
  have eq2639 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 y) y) ∨ y = (M.op (M.op (M.op X1 X2) y) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 y X1 y
       have i₂ := eq2606 X0 X1
       grind)
    | exact superpose eq2606 eq67
    | (have j1 := eq2606 X1 X2
       grind)
    | exact resolve eq67 eq2606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606
  have eq2701 : ∀ X0 X1 : G, y ≠ y ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have j0 := eq2639 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639
  have eq2702 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have j0 := eq2701 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2701
  have eq2756 : y = (M.op y y) := by
    first
    | (have i₁ := eq2702 (M.op x x) y
       have i₂ := eq2702 x x
       grind)
    | exact superpose eq2702 eq2702
    | exact resolve eq2702 eq2702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq2790 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq440 y x
       have i₂ := eq2756
       grind)
    | exact superpose eq2756 eq440
    | exact resolve eq440 eq2756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq2902 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op (σ y) X0) (σ y)
       have i₂ := eq2790 X0
       grind)
    | exact superpose eq2790 eq12
    | (have j0 := eq12 (M.op (σ y) X0) (σ y)
       grind)
    | (have r₁ := eq12 (M.op (σ y) X0) (σ y)
       have r₂ := eq2790 X0
       grind)
    | exact resolve eq12 eq2790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2790
  have eq2915 : ∀ X0 : G, (k (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2902 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902
  have eq3577 : ∀ X0 : G, (k (τ (M.op (σ y) X0)) y) = (τ (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ y) X0) y
       have i₂ := eq2915 X0
       grind)
    | exact superpose eq2915 eq22
    | exact resolve eq22 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2915
  have eq3702 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (k (τ (M.op (σ y) (M.op X0 (σ y)))) y) := by
    intro X0
    first
    | (have i₁ := eq3577 (M.op X0 (σ y))
       have i₂ := eq67 (σ y) (σ y) X0
       grind)
    | exact superpose eq67 eq3577
    | exact resolve eq3577 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq3577
  have eq7412 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1917 x y
       have i₂ := eq2080
       grind)
    | exact superpose eq2080 eq1917
    | (have j0 := eq1917 x y
       grind)
    | exact resolve eq1917 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917 eq2080
  have eq7419 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq7412
  have eq7420 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7419
  have eq7440 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq7420
       grind)
    | exact superpose eq7420 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7420
       grind)
    | exact resolve eq12 eq7420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7443 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 y x X0
       have i₂ := eq7420
       grind)
    | exact superpose eq7420 eq61
    | exact resolve eq61 eq7420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq7420
  have eq7458 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7440
  have eq7470 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7443 y
       have i₂ := eq2062
       grind)
    | exact superpose eq2062 eq7443
    | exact resolve eq7443 eq2062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062 eq7443
  have eq7507 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7470
  have eq7512 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq7507
       have i₂ := eq2756
       grind)
    | exact superpose eq2756 eq7507
    | exact resolve eq7507 eq2756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7507
  have eq7520 : (σ x) = (M.op (σ (M.op x x)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq439 x (σ y)
       have i₂ := eq7512
       grind)
    | exact superpose eq7512 eq439
    | exact resolve eq439 eq7512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq7512
  have eq7748 : (τ (σ x)) = (k (τ (M.op (σ y) (σ x))) y) ∨ x = y := by
    first
    | (have i₁ := eq3702 (σ (M.op x x))
       have i₂ := eq7520
       grind)
    | exact superpose eq7520 eq3702
    | exact resolve eq3702 eq7520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3702 eq7520
  have eq7785 : x = (k (τ (M.op (σ y) (σ x))) y) ∨ x = y := by
    first
    | (have i₁ := eq7748
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7748
    | exact resolve eq7748 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7748
  have eq8011 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1872
       have i₂ := eq7458
       grind)
    | exact superpose eq7458 eq1872
    | exact resolve eq1872 eq7458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872 eq7458
  have eq8016 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8011
  have eq8017 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8016
  have eq8022 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8017
       grind)
    | exact superpose eq8017 eq16
    | exact resolve eq16 eq8017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8033 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq8017
       grind)
    | exact superpose eq8017 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8017
       grind)
    | exact resolve eq13 eq8017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8017
  have eq8053 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
  clear eq8033
  have eq8057 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8053
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq8053
    | exact resolve eq8053 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8053
  have eq8626 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1122 x y
       have i₂ := eq8057
       grind)
    | exact superpose eq8057 eq1122
    | (have j0 := eq1122 x y
       grind)
    | exact resolve eq1122 eq8057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122 eq8057
  have eq8687 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq8626
       have r₂ := eq8022
       grind)
    | exact resolve eq8626 eq8022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8626
  have eq8732 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq8022
       have i₂ := eq8687
       grind)
    | exact superpose eq8687 eq8022
    | exact resolve eq8022 eq8687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8022 eq8687
  have eq8767 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq8732
  have eq8776 : x = (k (τ (σ y)) y) ∨ x = y := by
    first
    | (have i₁ := eq7785
       have i₂ := eq8767
       grind)
    | exact superpose eq8767 eq7785
    | exact resolve eq7785 eq8767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7785 eq8767
  have eq8839 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq8776
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8776
    | exact resolve eq8776 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8776
  have eq8853 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq8839
       have i₂ := eq350 y
       grind)
    | exact superpose eq350 eq8839
    | exact resolve eq8839 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350 eq8839
  have eq8859 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8853
       have i₂ := eq2756
       grind)
    | exact superpose eq2756 eq8853
    | exact resolve eq8853 eq2756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2756 eq8853
  have eq8860 : x = y := by grind
  clear eq8859
  have eq8864 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8860
       grind)
    | exact superpose eq8860 eq16
    | exact resolve eq16 eq8860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8860
  have eq8977 : False := by grind
  exact eq8977

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pyy_x_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq20 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq38 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (σ X1)) ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq184 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq77 x y
       grind)
    | exact superpose eq77 eq16
    | (have j1 := eq77 x y
       grind)
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X1) (σ X0) X2
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X0
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (M.op (σ (k X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X0) (σ X1) x
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq20
    | (have j1 := eq77 X1 X0
       grind)
    | exact resolve eq20 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq187 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq187 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq187 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq224 : ∀ X0 X1 X2 X3 : G, (σ (k (k X0 (τ X1)) (k X2 (τ X3)))) = (k (k (σ X0) X1) (k (σ X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38 X2 X3 (k X0 (τ X1))
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq38
    | exact resolve eq38 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq1377 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ X1)) ∨ (σ (σ (k X0 X1))) = (M.op (σ (σ X1)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq202 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq202
    | (have j0 := eq202 (σ X0) (σ X1)
       grind)
    | exact resolve eq202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1945 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ (k X1 X0)) (M.op (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq190 X1 X0 X2
       grind)
    | exact superpose eq190 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq190 X1 X0 X2
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq190 X0 X1 X2
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq190 X0 X0 X2
       grind)
    | exact resolve eq12 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq1960 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ (k X1 X0)) (M.op (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1945 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq1961 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X1 X0)) (M.op (σ X1) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1960 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1960
    | (have j0 := eq1960 X0 X1 X2
       grind)
    | exact resolve eq1960 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960
  have eq2248 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (M.op (σ (k X1 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq191 X1 X0 X2
       grind)
    | exact superpose eq191 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq191 X1 X0 X2
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq191 X0 X1 X2
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq191 X0 X0 X2
       grind)
    | exact resolve eq12 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq2263 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (M.op (σ (k X1 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2248 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248
  have eq2264 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (M.op (σ (k X1 X0)) X2)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2263 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2263
    | (have j0 := eq2263 X0 X1 X2
       grind)
    | exact resolve eq2263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq3418 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78
    | exact resolve eq78 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3443 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq78 X0 X1
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 (σ X0) X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) X0
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq78 (σ X1) X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3444 : ∀ X0 X1 X2 : G, (k X0 (τ X2)) = (τ (M.op X2 (σ X0))) ∨ (M.op (M.op X1 X2) (σ X0)) = X2 ∨ (M.op X2 (σ X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 X2 (σ X0)
       have i₂ := eq78 X2 X0
       grind)
    | exact superpose eq78 eq19
    | (have j1 := eq78 X2 X0
       grind)
    | exact resolve eq19 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3464 : ∀ X0 X1 : G, (σ X1) ≠ X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq78 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq3466 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3443 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq3472 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op X1 (σ X0))) ∨ (σ X0) = (k (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3466 X0 X1
       have j1 := eq3464 X1 X0
       grind)
    | (have r₁ := eq3466 X1 X1
       have r₂ := eq3464 (k (σ X1) X1) X1
       grind)
    | (have r₁ := eq3466 X1 X0
       have r₂ := eq3464 X0 X1
       grind)
    | (have r₁ := eq3466 X0 (σ X1)
       have r₂ := eq3464 (σ X0) X1
       grind)
    | exact resolve eq3466 eq3464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3464 eq3466
  have eq3475 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3418 X0 X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq3418
    | (have j0 := eq3418 X0 X1
       grind)
    | exact resolve eq3418 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3418
  have eq3564 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq3475 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475
  have eq3587 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3564 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564
  have eq3608 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3587 (M.op x x)
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq3587
    | (have j0 := eq3587 X0
       grind)
    | exact resolve eq3587 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3612 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq3587 X0
       grind)
    | exact superpose eq3587 eq12
    | (have j1 := eq3587 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3587 X0
       grind)
    | exact resolve eq12 eq3587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587
  have eq3639 : ∀ X0 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3612 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3612
  have eq3659 : ∀ X0 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3639 X0
       grind)
    | exact superpose eq3639 eq11
    | (have j1 := eq3639 X0
       grind)
    | exact resolve eq11 eq3639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3639
  have eq3766 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3659 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3659
    | (have j0 := eq3659 X0
       grind)
    | exact resolve eq3659 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3659
  have eq3875 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3766 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3766
  have eq4118 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq3608 X0
       grind)
    | exact superpose eq3608 eq12
    | (have j1 := eq3608 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3608 X0
       grind)
    | exact resolve eq12 eq3608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3608
  have eq4146 : ∀ X0 : G, (τ X0) = (τ (k (M.op X0 X0) (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4118 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4118
  have eq4565 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4146 (σ x)
       have i₂ := eq77 x x
       grind)
    | exact superpose eq77 eq4146
    | (have j0 := eq4146 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | exact resolve eq4146 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq4146
  have eq4627 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4565
  have eq4682 : ∀ X0 : G, (τ (σ X0)) = (τ (k (σ (k X0 X0)) (σ (k X0 X0)))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq4627 X0
       have j1 := eq3875 (σ X0)
       grind)
    | (have r₁ := eq4627 X0
       have r₂ := eq3875 (σ X0)
       grind)
    | exact resolve eq4627 eq3875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3875 eq4627
  have eq4689 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ (k X0 X0))) (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4682 X0
       have i₂ := eq32 (σ (k X0 X0)) (k X0 X0)
       grind)
    | exact superpose eq32 eq4682
    | (have j0 := eq4682 X0
       grind)
    | exact resolve eq4682 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4682
  have eq4695 : ∀ X0 : G, (τ (σ X0)) = (k (k X0 X0) (k X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4689 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq4689
    | (have j0 := eq4689 X0
       grind)
    | exact resolve eq4689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4689
  have eq4701 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq4695 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4695
    | (have j0 := eq4695 X0
       grind)
    | exact resolve eq4695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4695
  have eq4707 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4701 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq4701
    | (have j0 := eq4701 X0
       grind)
    | exact resolve eq4701 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4701
  have eq4856 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq224 (τ X0) X0 (τ X0) X0
       have i₂ := eq4707 (τ X0)
       grind)
    | exact superpose eq4707 eq224
    | (have j1 := eq4707 (τ X0)
       grind)
    | exact resolve eq224 eq4707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq4707
  have eq4883 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4856 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4856
    | (have j0 := eq4856 X0
       grind)
    | exact resolve eq4856 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4856
  have eq4893 : ∀ X0 : G, (σ (τ X0)) = (k (σ (τ X0)) X0) ∨ (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq4883 X0
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq4883
    | (have j0 := eq4883 X0
       grind)
    | exact resolve eq4883 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4883
  have eq4902 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4893 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4893
    | (have j0 := eq4893 X0
       grind)
    | exact resolve eq4893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4893
  have eq4909 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4902 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq4902
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq4902 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4943 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4909 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4909
  have eq5055 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4902 (M.op X0 X0)
       have i₂ := eq4943 X0
       grind)
    | exact superpose eq4943 eq4902
    | (have j1 := eq4943 X0
       grind)
    | exact resolve eq4902 eq4943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4902 eq4943
  have eq5075 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5055 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5055
  have eq5079 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5075 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq5075 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq5075 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5075
  have eq5179 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq198 X0 X0
       have i₂ := eq5079 X0
       grind)
    | exact superpose eq5079 eq198
    | (have j0 := eq198 X0 X0
       grind)
    | exact resolve eq198 eq5079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq5215 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5079 (σ X0)
       grind)
    | exact superpose eq5079 eq15
    | exact resolve eq15 eq5079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5227 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq5079 (τ X0)
       grind)
    | exact superpose eq5079 eq43
    | exact resolve eq43 eq5079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5263 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5179 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5179
  have eq5289 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5227 X0
       have i₂ := eq5079 X0
       grind)
    | exact superpose eq5079 eq5227
    | exact resolve eq5227 eq5079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5227
  have eq5297 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5215 X0
       have i₂ := eq5079 X0
       grind)
    | exact superpose eq5079 eq5215
    | exact resolve eq5215 eq5079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5079 eq5215
  have eq5691 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 (σ X0) (σ X0) x
       have i₂ := eq5297 X0
       grind)
    | exact superpose eq5297 eq20
    | exact resolve eq20 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq25994 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2264 X1 X0 (M.op (σ X0) x)
       have i₂ := eq1961 X1 X0 x
       grind)
    | exact superpose eq1961 eq2264
    | (have j0 := eq2264 X1 X0 x
       have j1 := eq1961 X1 X0 x
       grind)
    | exact resolve eq2264 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961 eq2264
  have eq26073 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq25994 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25994
  have eq26133 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq26073 X0 X1
       have i₂ := eq5297 X1
       grind)
    | exact superpose eq5297 eq26073
    | (have j0 := eq26073 X0 X1
       grind)
    | exact resolve eq26073 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26073
  have eq44962 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1377 (τ X1) (τ X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq1377
    | (have j0 := eq1377 (τ X0) (τ X1)
       grind)
    | exact resolve eq1377 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq45047 : ∀ X0 X1 : G, (σ X1) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq44962 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq44962
    | (have j0 := eq44962 X0 X1
       grind)
    | exact resolve eq44962 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44962
  have eq45112 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ (k X0 X1)))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq45047 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq45047
    | (have j0 := eq45047 X0 X1
       grind)
    | exact resolve eq45047 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45047
  have eq45169 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) = (σ (M.op (σ (τ X1)) (σ (τ X1)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq45112 X0 X1
       have i₂ := eq5297 (σ (τ X1))
       grind)
    | exact superpose eq5297 eq45112
    | (have j0 := eq45112 X0 X1
       grind)
    | exact resolve eq45112 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45112
  have eq45210 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) = (σ (σ (M.op (τ X1) (τ X1)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq45169 X0 X1
       have i₂ := eq5297 (τ X1)
       grind)
    | exact superpose eq5297 eq45169
    | (have j0 := eq45169 X0 X1
       grind)
    | exact resolve eq45169 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45169
  have eq45235 : ∀ X0 X1 : G, (σ (σ (τ (k X0 X1)))) = (σ (σ (τ (M.op X1 X1)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq45210 X0 X1
       have i₂ := eq5289 X1
       grind)
    | exact superpose eq5289 eq45210
    | (have j0 := eq45210 X0 X1
       grind)
    | exact resolve eq45210 eq5289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5289 eq45210
  have eq45259 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (τ (k X0 X1)))) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq45235 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq45235
    | (have j0 := eq45235 X0 X1
       grind)
    | exact resolve eq45235 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45235
  have eq45277 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq45259 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq45259
    | (have j0 := eq45259 X0 X1
       grind)
    | exact resolve eq45259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45259
  have eq45295 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (σ (τ X1))) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45277 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq45277
    | (have j0 := eq45277 X0 X1
       grind)
    | exact resolve eq45277 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45277
  have eq45306 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq45295 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq45295
    | (have j0 := eq45295 X0 X1
       grind)
    | exact resolve eq45295 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45295
  have eq105164 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3472 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3472
    | exact resolve eq3472 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472
  have eq105423 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq105164 X0 X1
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq105164
    | (have j0 := eq105164 X0 X1
       grind)
    | exact resolve eq105164 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105164
  have eq106173 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq105423 X1 X0
       grind)
    | exact superpose eq105423 eq11
    | (have j1 := eq105423 X1 X0
       grind)
    | exact resolve eq11 eq105423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105423
  have eq106351 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq106173 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq106173
    | (have j0 := eq106173 X0 X1
       grind)
    | exact resolve eq106173 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106173
  have eq106802 : ∀ X0 X1 : G, (τ X1) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq106351 X0 (τ X1)
       grind)
    | exact superpose eq106351 eq17
    | (have j1 := eq106351 X0 (τ X1)
       grind)
    | exact resolve eq17 eq106351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106351
  have eq128500 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq106802 X1 X0
       grind)
    | exact superpose eq106802 eq17
    | (have j1 := eq106802 X1 X0
       grind)
    | exact resolve eq17 eq106802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq106802
  have eq128839 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq128500 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq128500
    | (have j0 := eq128500 X0 X1
       grind)
    | exact resolve eq128500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128500
  have eq129163 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X1 (τ (σ X0)))) ∨ (M.op X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq128839 (σ X0) X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq128839
    | (have j0 := eq128839 (σ X0) X1
       grind)
    | exact resolve eq128839 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128839
  have eq129539 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 (τ (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq129163 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq129163
    | (have j0 := eq129163 X0 X1
       grind)
    | exact resolve eq129163 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129163
  have eq129646 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq129539 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq129539
    | (have j0 := eq129539 X0 X1
       grind)
    | exact resolve eq129539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129539
  have eq130413 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq184
       have i₂ := eq129646 y x
       grind)
    | exact superpose eq129646 eq184
    | (have j1 := eq129646 y x
       grind)
    | (have r₁ := eq184
       have r₂ := eq129646 y x
       grind)
    | exact resolve eq184 eq129646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129646
  have eq130636 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq130413
  have eq130685 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq197 x y
       grind)
    | (have r₁ := eq130636
       have r₂ := eq197 x y
       grind)
    | exact resolve eq130636 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq130636
  have eq132289 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 x y
       have i₂ := eq130685
       grind)
    | exact superpose eq130685 eq19
    | exact resolve eq19 eq130685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130685
  have eq159560 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq132289 (M.op x x)
       have i₂ := eq132289 x
       grind)
    | exact superpose eq132289 eq132289
    | exact resolve eq132289 eq132289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132289
  have eq159670 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq159560
  have eq159714 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq159670
       grind)
    | exact superpose eq159670 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq159670
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq159670
       grind)
    | exact resolve eq13 eq159670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159782 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq159670
  have eq159788 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq159714
  have eq159834 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq159788
       have r₂ := eq159782
       grind)
    | exact resolve eq159788 eq159782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159782 eq159788
  have eq159892 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq159834
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq159834
    | exact resolve eq159834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159834
  have eq161040 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (σ x) (σ y)
       have i₂ := eq159892
       grind)
    | exact superpose eq159892 eq19
    | exact resolve eq19 eq159892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159892
  have eq163341 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq161040 (M.op x (σ x))
       have i₂ := eq161040 x
       grind)
    | exact superpose eq161040 eq161040
    | exact resolve eq161040 eq161040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161040
  have eq163521 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ x = (M.op x x) := by grind
  clear eq163341
  have eq163548 : x = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq163521
       have i₂ := eq5297 x
       grind)
    | exact superpose eq5297 eq163521
    | exact resolve eq163521 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163521
  have eq164032 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5263 x
       have i₂ := eq163548
       grind)
    | exact superpose eq163548 eq5263
    | (have j0 := eq5263 x
       grind)
    | (have r₁ := eq5263 x
       have r₂ := eq163548
       grind)
    | exact resolve eq5263 eq163548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163548
  have eq164169 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq164032
  have eq164182 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have j1 := eq5263 x
       grind)
    | (have r₁ := eq164169
       have r₂ := eq5263 x
       grind)
    | exact resolve eq164169 eq5263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5263 eq164169
  have eq164195 : (σ x) = (σ (M.op x x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq164182
       have i₂ := eq5297 x
       grind)
    | exact superpose eq5297 eq164182
    | exact resolve eq164182 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164182
  have eq164206 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ y) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq5691 x x
       have i₂ := eq164195
       grind)
    | exact superpose eq164195 eq5691
    | exact resolve eq5691 eq164195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5691
  have eq164224 : (τ (σ x)) = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq164195
       grind)
    | exact superpose eq164195 eq10
    | exact resolve eq10 eq164195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164547 : x = (M.op x x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq164224
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq164224
    | exact resolve eq164224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164224
  have eq185885 : ∀ X0 X1 X2 : G, (k (τ X0) (τ X1)) = (τ (M.op X1 X0)) ∨ (M.op (M.op X2 X1) X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3444 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3444
    | exact resolve eq3444 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3444
  have eq186194 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op (M.op X2 X1) X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq185885 X0 X1 X2
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq185885
    | (have j0 := eq185885 X0 X1 X2
       grind)
    | exact resolve eq185885 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq185885
  have eq284557 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26133 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305683 : ∀ X0 X1 X2 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ (M.op (M.op X2 X0) X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq186194 X1 X0 X2
       grind)
    | exact superpose eq186194 eq11
    | (have j1 := eq186194 X1 X0 X2
       grind)
    | exact resolve eq11 eq186194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186194
  have eq305910 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq305683 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq305683
    | (have j0 := eq305683 X0 X1 X2
       grind)
    | exact resolve eq305683 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305683
  have eq306810 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x X0) = (k X0 x) ∨ x = (M.op x X0) ∨ (σ y) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq305910 x X0 x
       have i₂ := eq164547
       grind)
    | exact superpose eq164547 eq305910
    | (have j0 := eq305910 x X0 x
       grind)
    | exact resolve eq305910 eq164547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164547 eq305910
  have eq307189 : ∀ X0 : G, (σ y) = (σ (k y x)) ∨ (M.op x X0) = (k X0 x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq306810 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306810
  have eq308814 : ∀ X0 : G, (k y x) = (τ (σ y)) ∨ (M.op x X0) = (k X0 x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq307189 X0
       grind)
    | exact superpose eq307189 eq10
    | (have j1 := eq307189 X0
       grind)
    | exact resolve eq10 eq307189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307189
  have eq309268 : ∀ X0 : G, y = (k y x) ∨ (M.op x X0) = (k X0 x) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq308814 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq308814
    | (have j0 := eq308814 X0
       grind)
    | exact resolve eq308814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308814
  have eq309363 : y ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq309268 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309268
  have eq309376 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq309363
       have r₂ := eq14 y x
       grind)
    | exact resolve eq309363 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309363
  have eq310164 : x ≠ x ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq309376
       grind)
    | exact superpose eq309376 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq309376
       grind)
    | exact resolve eq12 eq309376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310165 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq19 X0 x y
       have i₂ := eq309376
       grind)
    | exact superpose eq309376 eq19
    | exact resolve eq19 eq309376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq310226 : (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq310164
  have eq310238 : x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq310165 (M.op x x)
       have i₂ := eq310165 x
       grind)
    | exact superpose eq310165 eq310165
    | exact resolve eq310165 eq310165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310165
  have eq310388 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  clear eq310238
  have eq312860 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq310226
  have eq312873 : x ≠ (M.op x x) ∨ x = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq312860
       have i₂ := eq309376
       grind)
    | exact superpose eq309376 eq312860
    | exact resolve eq312860 eq309376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312860
  have eq312875 : x = (k y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq312873
       have r₂ := eq310388
       grind)
    | exact resolve eq312873 eq310388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310388 eq312873
  have eq313366 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq312875
  have eq313388 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq313366
       have r₂ := eq309376
       grind)
    | exact resolve eq313366 eq309376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309376 eq313366
  have eq313415 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184
       have i₂ := eq313388
       grind)
    | exact superpose eq313388 eq184
    | exact resolve eq184 eq313388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq313521 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq313415
  have eq325961 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq313521
       have i₂ := eq26133 y x
       grind)
    | exact superpose eq26133 eq313521
    | (have j1 := eq26133 y x
       grind)
    | exact resolve eq313521 eq26133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26133
  have eq325964 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq313521
       grind)
    | exact superpose eq313521 eq16
    | exact resolve eq16 eq313521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325965 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq164206 (σ y)
       have i₂ := eq313521
       grind)
    | exact superpose eq313521 eq164206
    | exact resolve eq164206 eq313521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164206
  have eq326025 : (σ x) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq313521
       grind)
    | exact superpose eq313521 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq313521
       grind)
    | exact resolve eq12 eq313521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313521
  have eq326122 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by grind
  clear eq325965
  have eq326177 : (σ x) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq326025
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq326025 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326025
  have eq326208 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq326122
       have i₂ := eq313388
       grind)
    | exact superpose eq313388 eq326122
    | exact resolve eq326122 eq313388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326122
  have eq326209 : (σ x) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq284557 x y
       grind)
    | (have r₁ := eq325961
       have r₂ := eq284557 x y
       grind)
    | exact resolve eq325961 eq284557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284557 eq325961
  have eq326253 : (k (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq326177
       have i₂ := eq5297 x
       grind)
    | exact superpose eq5297 eq326177
    | exact resolve eq326177 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326177
  have eq326272 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq326208
       have r₂ := eq325964
       grind)
    | exact resolve eq326208 eq325964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325964 eq326208
  have eq326273 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq45306 y x
       grind)
    | (have r₁ := eq326209
       have r₂ := eq45306 y x
       grind)
    | exact resolve eq326209 eq45306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45306 eq326209
  have eq326312 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq326253
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq326253
    | exact resolve eq326253 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326253
  have eq326324 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq326273
       have i₂ := eq313388
       grind)
    | exact superpose eq313388 eq326273
    | exact resolve eq326273 eq313388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326273
  have eq326327 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq326312
       have i₂ := eq313388
       grind)
    | exact superpose eq313388 eq326312
    | exact resolve eq326312 eq313388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326312
  have eq326331 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq326324
       have i₂ := eq326272
       grind)
    | exact superpose eq326272 eq326324
    | exact resolve eq326324 eq326272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326324
  have eq326333 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq326331
       have r₂ := eq326327
       grind)
    | exact resolve eq326331 eq326327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326327 eq326331
  have eq327846 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq326272
       grind)
    | exact superpose eq326272 eq16
    | exact resolve eq16 eq326272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326272
  have eq328029 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq327846
       have i₂ := eq326333
       grind)
    | exact superpose eq326333 eq327846
    | exact resolve eq327846 eq326333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327846
  have eq328091 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq328029
       have i₂ := eq164195
       grind)
    | exact superpose eq164195 eq328029
    | (have r₁ := eq328029
       have r₂ := eq164195
       grind)
    | exact resolve eq328029 eq164195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164195
  have eq328094 : (σ y) = (σ (k y x)) := by grind
  clear eq328091
  have eq328101 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq328094
       have i₂ := eq313388
       grind)
    | exact superpose eq313388 eq328094
    | exact resolve eq328094 eq313388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313388 eq328094
  have eq329282 : (M.op x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq328101
       grind)
    | exact superpose eq328101 eq10
    | exact resolve eq10 eq328101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329580 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq5297 (M.op x y)
       have i₂ := eq328101
       grind)
    | exact superpose eq328101 eq5297
    | exact resolve eq5297 eq328101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328101
  have eq329669 : (σ (M.op y y)) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq329580
       have i₂ := eq5297 y
       grind)
    | exact superpose eq5297 eq329580
    | exact resolve eq329580 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329580
  have eq329750 : y = (M.op x y) := by
    first
    | (have i₁ := eq329282
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq329282
    | exact resolve eq329282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329282
  have eq329801 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq19 x y X0
       have i₂ := eq329750
       grind)
    | exact superpose eq329750 eq19
    | exact resolve eq19 eq329750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331586 : y = (M.op y y) := by
    first
    | (have i₁ := eq329801 (M.op y x)
       have i₂ := eq329801 x
       grind)
    | exact superpose eq329801 eq329801
    | exact resolve eq329801 eq329801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329801
  have eq336063 : (M.op x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq326333
       grind)
    | exact superpose eq326333 eq10
    | exact resolve eq10 eq326333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336362 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq5297 (M.op x y)
       have i₂ := eq326333
       grind)
    | exact superpose eq326333 eq5297
    | exact resolve eq5297 eq326333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326333
  have eq336482 : (σ (M.op y y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq336362
       have i₂ := eq329669
       grind)
    | exact superpose eq329669 eq336362
    | exact resolve eq336362 eq329669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329669 eq336362
  have eq336759 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq336063
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq336063
    | exact resolve eq336063 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336063
  have eq336799 : (σ (M.op y y)) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq336482
       have i₂ := eq5297 (M.op x x)
       grind)
    | exact superpose eq5297 eq336482
    | exact resolve eq336482 eq5297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5297 eq336482
  have eq337076 : y = (M.op x x) := by
    first
    | (have i₁ := eq336759
       have i₂ := eq329750
       grind)
    | exact superpose eq329750 eq336759
    | exact resolve eq336759 eq329750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329750 eq336759
  have eq337106 : (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq336799
       have i₂ := eq19 x x x
       grind)
    | (have i₁ := eq336799
       have i₂ := eq19 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq19 eq336799
    | exact resolve eq336799 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq336799
  have eq337338 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq337106
       have i₂ := eq331586
       grind)
    | exact superpose eq331586 eq337106
    | exact resolve eq337106 eq331586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331586 eq337106
  have eq338789 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq328029
       have i₂ := eq337076
       grind)
    | exact superpose eq337076 eq328029
    | exact resolve eq328029 eq337076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328029 eq337076
  have eq339107 : False := by grind
  exact eq339107

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_y_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq29 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq41 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29
    | (have j0 := eq29 x
       grind)
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq53 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq54 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq64 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq77 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq53 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y X0
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq53 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 X0 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq53 X2 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq80 eq53
    | exact resolve eq53 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq145 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq187 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq145 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq145
    | exact resolve eq145 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq663 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op x x)
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq670 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq670 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq670 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq679 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq187 X0 X0
       have i₂ := eq671 X0
       grind)
    | exact superpose eq671 eq187
    | exact resolve eq187 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq681 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq671 (σ X0)
       grind)
    | exact superpose eq671 eq15
    | exact resolve eq15 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq681 X0
       have i₂ := eq671 X0
       grind)
    | exact superpose eq671 eq681
    | exact resolve eq681 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq684 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq679 X0
       have i₂ := eq671 (τ X0)
       grind)
    | exact superpose eq671 eq679
    | exact resolve eq679 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq679
  have eq12072 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq88 eq663
    | (have j0 := eq663 (M.op x y) x
       grind)
    | (have r₁ := eq663 (M.op x y) x
       have r₂ := eq88 (M.op x y)
       grind)
    | exact resolve eq663 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12073 : y ≠ y ∨ y = (M.op y y) ∨ y = (k (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq77 eq663
    | (have j0 := eq663 y (M.op x y)
       grind)
    | (have r₁ := eq663 y (M.op x y)
       have r₂ := eq77 y
       grind)
    | exact resolve eq663 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq12078 : y = (k (M.op x y) (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq12073
  have eq12079 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq12072
  have eq12104 : (σ y) = (σ (M.op y y)) ∨ (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ (M.op x y)) (σ (M.op y y))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq12078 eq108
    | (have j0 := eq108 (M.op y y) (M.op x y)
       grind)
    | exact resolve eq108 eq12078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12078
  have eq12111 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ (M.op x y)) (σ (M.op y y))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12104
       have i₂ := eq682 y
       grind)
    | exact superpose eq682 eq12104
    | exact resolve eq12104 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12104
  have eq12114 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op (σ (M.op x y)) (σ (M.op y y))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12111
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12111
    | exact resolve eq12111 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12111
  have eq12115 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12114
       have i₂ := eq682 y
       grind)
    | exact superpose eq682 eq12114
    | exact resolve eq12114 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12114
  have eq12116 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12115
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12115
    | exact resolve eq12115 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12115
  have eq12117 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq12116
    | exact resolve eq12116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12116
  have eq12118 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12117
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq12117
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq12117
    | exact resolve eq12117 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12117
  have eq12119 : (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12118
       have i₂ := eq682 y
       grind)
    | exact superpose eq682 eq12118
    | exact resolve eq12118 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12118
  have eq12120 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12119
       have i₂ := eq53 (σ y) (σ y) (σ y)
       grind)
    | (have i₁ := eq12119
       have i₂ := eq53 x (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) x
       grind)
    | exact superpose eq53 eq12119
    | exact resolve eq12119 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12119
  have eq12121 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq12120
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12120
    | exact resolve eq12120 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12120
  have eq12122 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq12121
  have eq12146 : (σ (M.op x y)) = (σ (M.op (M.op x y) (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq12079 eq108
    | (have j0 := eq108 (M.op (M.op x y) (M.op x y)) x
       grind)
    | exact resolve eq108 eq12079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq12079
  have eq12153 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12146
       have i₂ := eq682 sF0
       grind)
    | exact superpose eq682 eq12146
    | exact resolve eq12146 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12146
  have eq12156 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq12153
    | exact resolve eq12153 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12153
  have eq12157 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12156
       have i₂ := eq682 sF0
       grind)
    | exact superpose eq682 eq12156
    | exact resolve eq12156 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12156
  have eq12158 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq12157
    | exact resolve eq12157 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12157
  have eq12159 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12158
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12158
    | exact resolve eq12158 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12158
  have eq12160 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12159
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq12159
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq12159
    | exact resolve eq12159 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12159
  have eq12161 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12160
       have i₂ := eq682 sF0
       grind)
    | exact superpose eq682 eq12160
    | exact resolve eq12160 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12160
  have eq12162 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12161
       have i₂ := eq53 (σ sF0) (σ sF0) (σ sF0)
       grind)
    | (have i₁ := eq12161
       have i₂ := eq53 x (M.op (M.op (σ sF0) (σ sF0)) (M.op (σ sF0) (σ sF0))) x
       grind)
    | exact superpose eq53 eq12161
    | exact resolve eq12161 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq12161
  have eq12163 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq12162
    | exact resolve eq12162 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12162
  have eq12164 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq12163
  have eq69179 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq12122 eq54
    | exact resolve eq54 eq12122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12122
  have eq69419 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq12164 eq54
    | exact resolve eq54 eq12164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12164
  have eq71358 : ∀ X0 : G, (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq69179 eq684
    | (have j1 := eq69179 X0
       grind)
    | exact resolve eq684 eq69179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69179
  have eq71365 : ∀ X0 : G, y = (M.op y y) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39 eq71358
    | (have j0 := eq71358 X0
       grind)
    | exact resolve eq71358 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq71358
  have eq71366 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq71365 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71365
  have eq73381 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq71366 eq69419
    | exact resolve eq69419 eq71366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69419
  have eq73390 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq73381
    | exact resolve eq73381 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73381
  have eq73391 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq73390
       have r₂ := eq27
       grind)
    | exact resolve eq73390 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73390
  have eq73405 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq73391 eq684
    | exact resolve eq684 eq73391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684 eq73391
  have eq73422 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq37 eq73405
    | exact resolve eq73405 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq73405
  have eq73423 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op y y) := by grind
  clear eq73422
  have eq73434 : y = (M.op y y) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq73423 eq88
    | exact resolve eq88 eq73423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq73423
  have eq73460 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq94 y x
       have i₂ := eq73434
       grind)
    | exact superpose eq73434 eq94
    | (have r₁ := eq94 y x
       have r₂ := eq73434
       grind)
    | exact resolve eq94 eq73434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73461 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq682 y
       have i₂ := eq73434
       grind)
    | exact superpose eq73434 eq682
    | exact resolve eq682 eq73434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73434
  have eq73471 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq73460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73460
  have eq73475 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq73461
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq73461
    | exact resolve eq73461 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73461
  have eq73550 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq73475 eq94
    | (have r₁ := eq94 (σ y) x
       have r₂ := eq73475
       grind)
    | exact resolve eq94 eq73475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73475
  have eq73561 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq73550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73550
  have eq74751 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq73561 eq64
    | exact resolve eq64 eq73561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq73561
  have eq74953 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq26 eq74751
    | exact resolve eq74751 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74751
  have eq74991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq74953
       have i₂ := eq73471 x
       grind)
    | exact superpose eq73471 eq74953
    | exact resolve eq74953 eq73471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73471 eq74953
  have eq75043 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by grind
  clear eq74991
  have eq75053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq75043
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75043
    | exact resolve eq75043 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq75043
  have eq75062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq20 eq75053
    | exact resolve eq75053 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75053
  have eq75068 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have r₁ := eq75062
       have r₂ := eq27
       grind)
    | exact resolve eq75062 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75062
  have eq75075 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq75068 eq83
    | exact resolve eq83 eq75068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq75077 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq75068 eq82
    | exact resolve eq82 eq75068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq75092 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq75068 eq75077
    | exact resolve eq75077 eq75068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75077
  have eq75607 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq75092 eq94
    | (have r₁ := eq94 (M.op x y) x
       have r₂ := eq75092
       grind)
    | exact resolve eq94 eq75092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75608 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq75092 eq682
    | exact resolve eq682 eq75092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq75092
  have eq75618 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq75607 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75607
  have eq75658 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq75608
    | exact resolve eq75608 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75608
  have eq84006 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq75618 eq41
    | exact resolve eq41 eq75618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq75618
  have eq84143 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq75068 eq84006
    | exact resolve eq84006 eq75068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75068 eq84006
  have eq88765 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq84143
    | exact resolve eq84143 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84143
  have eq90260 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq75658 eq94
    | (have r₁ := eq94 (σ (M.op x y)) x
       have r₂ := eq75658
       grind)
    | exact resolve eq94 eq75658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq75658
  have eq90271 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq90260 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90260
  have eq91951 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq90271 eq88765
    | exact resolve eq88765 eq90271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88765 eq90271
  have eq94807 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq91951 eq54
    | exact resolve eq54 eq91951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq94811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq71366 eq94807
    | exact resolve eq94807 eq71366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71366 eq94807
  have eq94826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq94811
    | exact resolve eq94811 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94811
  have eq94829 : y = (M.op y y) := by
    first
    | (have r₁ := eq94826
       have r₂ := eq27
       grind)
    | exact resolve eq94826 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94826
  have eq95139 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq94829
       grind)
    | exact superpose eq94829 eq77
    | exact resolve eq77 eq94829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq94829
  have eq102066 : y = (M.op x y) := by
    first
    | exact superpose eq75075 eq95139
    | exact resolve eq95139 eq75075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75075 eq95139
  have eq105254 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq102066 eq20
    | exact resolve eq20 eq102066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq102066
  have eq111043 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq105254
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq105254
    | exact resolve eq105254 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq105254
  have eq111951 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq111043 eq26
    | exact resolve eq26 eq111043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq111043
  have eq115927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq91951 eq111951
    | exact resolve eq111951 eq91951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91951 eq111951
  have eq116452 : False := by grind
  exact eq116452

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pxy_pyy_Equation2164 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq19 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq18 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq21 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : (M.op x y) = (M.op x y) := by grind
  have eq25 : (M.op x y) = (M.op x y) := by grind
  clear eq24
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq27 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq26
  have eq28 : (σ x) = (σ x) := by grind
  have eq29 : (σ x) = (σ x) := by grind
  clear eq28
  have eq30 : (σ y) = (σ y) := by grind
  have eq31 : (σ y) = (σ y) := by grind
  clear eq30
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq33 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq32
  have eq34 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq35 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq19
    | (have j1 := eq20 X0
       grind)
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20
  have eq36 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq23 eq22
    | (have j1 := eq23 X0
       grind)
    | exact resolve eq22 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23
  have eq39 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq41 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq31
       grind)
    | exact superpose eq31 eq35
    | (have j0 := eq35 y
       grind)
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq42 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq39
       grind)
    | exact superpose eq39 eq25
    | exact resolve eq25 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq39
  have eq43 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq41
       grind)
    | exact superpose eq41 eq42
    | exact resolve eq42 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq42
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq35 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq65 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq47 (τ X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq47
    | exact resolve eq47 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq27 eq47
    | (have j0 := eq47 (M.op x y) X0
       grind)
    | exact resolve eq47 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq27 eq69
    | (have j0 := eq69 (M.op x y)
       grind)
    | exact resolve eq69 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq89 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq122 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : ∀ X0 X1 : G, (k X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq134 : ∀ X0 X1 : G, (k X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq126
  have eq138 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq122
  have eq145 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq138
    | (have j0 := eq138 X0 X1
       grind)
    | exact resolve eq138 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq151 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (k (σ X0) (σ X0)) ∨ (k X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  clear eq145
  have eq175 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 X1 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq43 eq49
    | exact resolve eq49 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    grind
  have eq185 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq49 X2 X0 x
       grind)
    | exact superpose eq49 eq49
    | exact resolve eq49 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op X0 (τ (σ x))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq43 eq49
    | exact resolve eq49 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq194 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq199 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    grind
  clear eq194
  have eq207 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X1 X2)) = X1 ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    grind
  clear eq175
  have eq218 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq179 eq49
    | exact resolve eq49 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq179
  have eq226 : (M.op x y) = (M.op (k (M.op x y) (M.op x y)) (τ (σ y))) := by grind
  clear eq218
  have eq277 : (M.op x y) ≠ (M.op (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (σ y))) := by
    first
    | exact superpose eq226 eq13
    | (have j0 := eq13 (τ (σ y)) (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq280 : (M.op x y) ≠ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (σ y))) := by grind
  clear eq277
  have eq281 : (M.op x y) = (k (k (M.op x y) (M.op x y)) (τ (σ y))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq280
       have r₂ := eq199 (M.op x y)
       grind)
    | exact resolve eq280 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq283 : (τ (σ x)) = (M.op (k (τ (σ x)) (τ (σ x))) (M.op x y)) := by grind
  clear eq186
  have eq377 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (τ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq65
    | exact resolve eq65 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq425 : ∀ X0 X1 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X1)) := by
    intro X0 X1
    grind
  clear eq53
  have eq949 : (τ (σ x)) ≠ (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ x)) = (k (k (τ (σ x)) (τ (σ x))) (M.op x y)) := by
    first
    | exact superpose eq283 eq89
    | (have j0 := eq89 (M.op x y) (k (τ (σ x)) (τ (σ x)))
       grind)
    | exact resolve eq89 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq960 : (τ (σ x)) = (k (k (τ (σ x)) (τ (σ x))) (M.op x y)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have r₁ := eq949
       have r₂ := eq199 (τ (σ x))
       grind)
    | exact resolve eq949 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq1008 : (σ (M.op x y)) = (k (σ (k (M.op x y) (M.op x y))) (σ (τ (σ y)))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq281 eq15
    | exact resolve eq15 eq281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq1009 : (σ (M.op x y)) = (k (σ (k (M.op x y) (M.op x y))) (σ y)) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1008
       have i₂ := eq36 sF5
       grind)
    | exact superpose eq36 eq1008
    | exact resolve eq1008 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1011 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1009
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1009
    | exact resolve eq1009 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1012 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27 eq1011
    | exact resolve eq1011 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1447 : ∀ X0 X1 : G, (k X1 X1) = (M.op X1 (τ X0)) ∨ (k X0 X0) = (k (σ X1) X0) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq151 (τ X0) X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq151
    | (have j0 := eq151 (τ X0) X1
       grind)
    | exact resolve eq151 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq1625 : (σ (τ (σ x))) = (k (σ (k (τ (σ x)) (τ (σ x)))) (σ (M.op x y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq960 eq15
    | exact resolve eq15 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1629 : (σ (τ (σ x))) = (k (σ (k (τ (σ x)) (τ (σ x)))) (σ (M.op x y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq27 eq1625
    | exact resolve eq1625 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq1634 : (σ (τ (σ x))) = (k (k (σ (τ (σ x))) (σ (τ (σ x)))) (σ (M.op x y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq1629
       have i₂ := eq15 (τ sF4) (τ sF4)
       grind)
    | exact superpose eq15 eq1629
    | exact resolve eq1629 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629
  have eq1635 : (σ x) = (k (k (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq1634
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq1634
    | exact resolve eq1634 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634
  have eq2301 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (τ X1) = X0 ∨ (k X0 X0) = (k X0 (τ X1)) ∨ (k X1 X1) = (k (σ X0) X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X1 (τ X0)
       have i₂ := eq1447 X0 X1
       grind)
    | exact superpose eq1447 eq89
    | (have j0 := eq89 (τ X1) X0
       have j1 := eq1447 X1 X0
       grind)
    | (have r₁ := eq89 X1 (τ X0)
       have r₂ := eq1447 X0 X1
       grind)
    | exact resolve eq89 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447
  have eq2338 : ∀ X0 X1 : G, (k X0 X0) ≠ (k X0 X0) ∨ (τ X1) = X0 ∨ (k X0 X0) = (k X0 (τ X1)) ∨ (k X1 X1) = (k (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2301 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2301
  have eq2339 : ∀ X0 X1 : G, (k X1 X1) = (k (σ X0) X1) ∨ (k X0 X0) = (k X0 (τ X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2338 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338
  have eq3319 : ∀ X0 X1 : G, (k (k X0 X1) (k X0 X1)) = X1 ∨ (M.op X0 X1) = (k X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199 X1
       have i₂ := eq134 X1 X1
       grind)
    | (have i₁ := eq199 X1
       have i₂ := eq134 X0 X1
       grind)
    | exact superpose eq134 eq199
    | (have j1 := eq134 X0 X1
       grind)
    | exact resolve eq199 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq4420 : ∀ X0 X1 : G, (k X1 X0) = (τ (k (σ X0) (σ X0))) ∨ (k X1 X1) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 X0
       have i₂ := eq2339 X1 (σ X0)
       grind)
    | (have i₁ := eq47 X0 X0
       have i₂ := eq2339 X0 (σ X0)
       grind)
    | exact superpose eq2339 eq47
    | (have j1 := eq2339 X1 (σ X0)
       grind)
    | exact resolve eq47 eq2339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2339
  have eq4453 : ∀ X0 X1 : G, (k X0 X0) = (k X1 X0) ∨ (k X1 X1) = (k X1 (τ (σ X0))) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4420 X0 X1
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq4420
    | (have j0 := eq4420 X0 X1
       grind)
    | exact resolve eq4420 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq4420
  have eq4487 : ∀ X0 X1 : G, (k X1 X1) = (k X1 X0) ∨ (k X0 X0) = (k X1 X0) ∨ (τ (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4453 X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq4453
    | (have j0 := eq4453 X0 X1
       grind)
    | exact resolve eq4453 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4453
  have eq4517 : ∀ X0 X1 : G, (k X1 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4487 X0 X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq4487
    | (have j0 := eq4487 X0 X1
       grind)
    | exact resolve eq4487 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq4487
  have eq4697 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 (M.op (k X0 X1) X2)) ∨ X0 = X1 ∨ (k X0 X1) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq425 X1 X1
       have i₂ := eq4517 X0 X1
       grind)
    | (have i₁ := eq425 X0 X1
       have i₂ := eq4517 X0 X0
       grind)
    | exact superpose eq4517 eq425
    | (have j1 := eq4517 (k X0 X1) (M.op X0 (M.op (k X0 X1) X2))
       grind)
    | exact resolve eq425 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq47597 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X0) = (k X1 X0) ∨ (k X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4697 X1 X0 (M.op X0 x)
       have i₂ := eq207 X1 X0 x
       grind)
    | exact superpose eq207 eq4697
    | (have j0 := eq4697 (k X1 X0) (M.op X1 X0) x
       have j1 := eq207 X1 X0 x
       grind)
    | exact resolve eq4697 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq4697
  have eq47859 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X0) = (k X1 X0) ∨ (k X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47597 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47597
  have eq47926 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47859 X0 X1
       have j1 := eq89 (k X1 X0) (M.op X1 X0)
       grind)
    | (have r₁ := eq47859 X1 X1
       have r₂ := eq89 X1 X1
       grind)
    | (have r₁ := eq47859 (M.op X0 X1) (k X0 X0)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq47859 (k X0 X0) (M.op X0 X1)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq47859 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq47859
  have eq49022 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq33
       have i₂ := eq47926 sF5 sF4
       grind)
    | exact superpose eq47926 eq33
    | (have j1 := eq47926 (σ y) (σ x)
       grind)
    | exact resolve eq33 eq47926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47926
  have eq49174 : (σ y) = (k (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq49022 eq199
    | exact resolve eq199 eq49022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49022
  have eq51803 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq49174
       have i₂ := eq4517 sF5 sF4
       grind)
    | exact superpose eq4517 eq49174
    | (have j1 := eq4517 (σ y) (k (k (σ x) (σ x)) (k (σ x) (σ x)))
       grind)
    | exact resolve eq49174 eq4517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4517 eq49174
  have eq51867 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
  clear eq51803
  have eq51883 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq51867
       have i₂ := eq199 sF4
       grind)
    | exact superpose eq199 eq51867
    | exact resolve eq51867 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51867
  have eq51884 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq51883
  have eq52109 : (σ y) = (k (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq51884 eq199
    | exact resolve eq199 eq51884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51884
  have eq142724 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq1635 eq3319
    | (have j0 := eq3319 (k (σ x) (σ x)) (σ (M.op x y))
       grind)
    | exact resolve eq3319 eq1635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq142727 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1012 eq3319
    | (have j0 := eq3319 (k (σ (M.op x y)) (σ (M.op x y))) (σ y)
       grind)
    | exact resolve eq3319 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319
  have eq143002 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by grind
  clear eq142727
  have eq143004 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (M.op (k (σ x) (σ x)) (σ (M.op x y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by grind
  clear eq142724
  have eq143113 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq143002
       have i₂ := eq199 sF3
       grind)
    | exact superpose eq199 eq143002
    | exact resolve eq143002 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143002
  have eq143114 : (σ x) = (M.op (k (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq143004
       have i₂ := eq199 sF4
       grind)
    | exact superpose eq199 eq143004
    | exact resolve eq143004 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143004
  have eq143183 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq143113 eq185
    | exact resolve eq185 eq143113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq143113
  have eq146245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq143114 eq143183
    | exact resolve eq143183 eq143114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143183
  have eq146267 : (σ (M.op x y)) = (M.op (σ x) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq143114 eq183
    | exact resolve eq183 eq143114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq143114
  have eq146304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq33 eq146245
    | exact resolve eq146245 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146245
  have eq146306 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq146304
       have r₂ := eq34
       grind)
    | exact resolve eq146304 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146304
  have eq1163009 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq146306 eq199
    | exact resolve eq199 eq146306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146306
  have eq1163019 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1163009 eq36
    | exact resolve eq36 eq1163009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163009
  have eq1163020 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1163019
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1163019
    | exact resolve eq1163019 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163019
  have eq1163022 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq27 eq1163020
    | exact resolve eq1163020 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163020
  have eq1163023 : (τ (σ x)) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq1163022
  have eq1163030 : (σ x) = (σ (k (M.op x y) (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1163023 eq36
    | exact resolve eq36 eq1163023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163023
  have eq1163031 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1163030
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1163030
    | exact resolve eq1163030 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163030
  have eq1163034 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq1163031
    | exact resolve eq1163031 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163031
  have eq1163074 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1163034 eq199
    | exact resolve eq199 eq1163034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163034
  have eq1163143 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1163074 eq199
    | exact resolve eq199 eq1163074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163074
  have eq1163164 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq1163143
  have eq1163173 : (k (M.op x y) (M.op x y)) = (τ (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1163164 eq84
    | exact resolve eq84 eq1163164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq1163164
  have eq1163229 : (k (M.op x y) (M.op x y)) = (k (τ (k (σ y) (σ y))) (τ (k (σ y) (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1163173
       have i₂ := eq377 (k sF5 sF5) (k sF5 sF5)
       grind)
    | exact superpose eq377 eq1163173
    | exact resolve eq1163173 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163173
  have eq1163237 : (k (M.op x y) (M.op x y)) = (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1163229
       have i₂ := eq377 sF5 sF5
       grind)
    | exact superpose eq377 eq1163229
    | exact resolve eq1163229 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq1163229
  have eq1163243 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1163237
       have i₂ := eq199 (τ sF5)
       grind)
    | exact superpose eq199 eq1163237
    | exact resolve eq1163237 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163237
  have eq1163290 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1163243 eq36
    | exact resolve eq36 eq1163243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163243
  have eq1163297 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1163290
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1163290
    | exact resolve eq1163290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163290
  have eq1163302 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq1163297
    | exact resolve eq1163297 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163297
  have eq1163387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1163302 eq146267
    | exact resolve eq146267 eq1163302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146267 eq1163302
  have eq1164026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by grind
  clear eq1163387
  have eq1164088 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq33 eq1164026
    | exact resolve eq1164026 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164026
  have eq1164112 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have r₁ := eq1164088
       have r₂ := eq34
       grind)
    | exact resolve eq1164088 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164088
  have eq1167178 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq1164112 eq15
    | exact resolve eq15 eq1164112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164112
  have eq1167188 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1167178
       have i₂ := eq36 sF4
       grind)
    | exact superpose eq36 eq1167178
    | exact resolve eq1167178 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167178
  have eq1167221 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq27 eq1167188
    | exact resolve eq1167188 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167188
  have eq1167222 : (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq1167221
  have eq1167235 : (k (σ x) (σ x)) = (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (σ y)) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1167222 eq1012
    | exact resolve eq1012 eq1167222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1167620 : (k (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1167235
       have i₂ := eq199 sF4
       grind)
    | exact superpose eq199 eq1167235
    | exact resolve eq1167235 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167235
  have eq1173080 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1167620 eq52109
    | exact resolve eq52109 eq1167620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52109 eq1167620
  have eq1173098 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (τ (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1173080
       have i₂ := eq199 sF4
       grind)
    | exact superpose eq199 eq1173080
    | exact resolve eq1173080 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173080
  have eq1173099 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1173098
  have eq1174841 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1173099 eq36
    | exact resolve eq36 eq1173099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1173099
  have eq1174842 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1174841
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1174841
    | exact resolve eq1174841 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174841
  have eq1174845 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq1174842
    | exact resolve eq1174842 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1174842
  have eq1174846 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1167222 eq1174845
    | exact resolve eq1174845 eq1167222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174845
  have eq1174847 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1174846
       have i₂ := eq199 sF4
       grind)
    | exact superpose eq199 eq1174846
    | exact resolve eq1174846 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq1174846
  have eq1174848 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1174847
  have eq1174849 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1174848 eq34
    | exact resolve eq34 eq1174848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174848
  have eq1174996 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1174849
       have r₂ := eq1167222
       grind)
    | exact resolve eq1174849 eq1167222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174849
  have eq1175001 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1174996 eq33
    | exact resolve eq33 eq1174996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1174996
  have eq1176300 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1175001
  have eq1176549 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq1176300 eq34
    | exact resolve eq34 eq1176300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1176300
  have eq1177072 : False := by grind
  exact eq1177072

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxx_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq43 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 (k X0 X0) X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq35 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq35 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq41 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq54 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq42 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq42 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq42 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq49
    | (have j0 := eq49 X0 X1
       grind)
    | exact resolve eq49 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq49
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq43 X1 X0
       grind)
    | (have r₁ := eq54 X1 X0
       have r₂ := eq43 X0 X1
       grind)
    | (have r₁ := eq54 X0 (M.op X1 X1)
       have r₂ := eq43 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq54 X1 X1
       have r₂ := eq43 (k X1 X1) X1
       grind)
    | exact resolve eq54 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq54
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq56 X0 X1
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq56 X0 X1
       grind)
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq57
  have eq153 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq157 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq153 X0 X1
       have j1 := eq60 X1 X0
       grind)
    | (have r₁ := eq153 X1 X0
       have r₂ := eq60 X0 X1
       grind)
    | (have r₁ := eq153 X0 X0
       have r₂ := eq60 X0 X0
       grind)
    | exact resolve eq153 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq153
  have eq320 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq157 (σ X1) (σ X0)
       grind)
    | exact superpose eq157 eq15
    | exact resolve eq15 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq320 X0 X1
       have i₂ := eq157 X1 X0
       grind)
    | exact superpose eq157 eq320
    | exact resolve eq320 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq320
  have eq329 : False := by grind
  exact eq329
