import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3279`: `x ◇ x = y ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation3279 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3279 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3279.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq49 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq184 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48 x y
       grind)
    | exact superpose eq48 eq16
    | (have j1 := eq48 x y
       grind)
    | exact resolve eq16 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq1503 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1542 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1503 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1503
    | (have j0 := eq1503 X0 X1
       grind)
    | exact resolve eq1503 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq2342 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq184
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq184
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq184
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq184
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq184 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq2343 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2342
  have eq30792 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq2343
       grind)
    | exact superpose eq2343 eq16
    | exact resolve eq16 eq2343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30813 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2343
       grind)
    | exact superpose eq2343 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2343
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2343
       grind)
    | exact resolve eq13 eq2343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq30860 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq30813
  have eq30861 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq30860
  have eq30903 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq30861
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq30861
    | exact resolve eq30861 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30861
  have eq214879 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1542 y x
       have i₂ := eq30903
       grind)
    | exact superpose eq30903 eq1542
    | (have j0 := eq1542 y x
       grind)
    | exact resolve eq1542 eq30903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq214880 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq30903
       grind)
    | exact superpose eq30903 eq10
    | exact resolve eq10 eq30903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30903
  have eq214887 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq214879
  have eq214895 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq214880
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq214880
    | exact resolve eq214880 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214880
  have eq214896 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq214887
       have r₂ := eq30792
       grind)
    | exact resolve eq214887 eq30792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30792 eq214887
  have eq214899 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x (k y x)
       grind)
    | (have r₁ := eq214895
       have r₂ := eq13 y x
       grind)
    | exact resolve eq214895 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214895
  have eq215771 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq191 x y
       have i₂ := eq214899
       grind)
    | exact superpose eq214899 eq191
    | (have j0 := eq191 x y
       grind)
    | exact resolve eq191 eq214899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq214899
  have eq215781 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq215771
  have eq215782 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq215781
  have eq215935 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq215782
       grind)
    | exact superpose eq215782 eq16
    | exact resolve eq16 eq215782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215782
  have eq216823 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq215935
       have i₂ := eq214896
       grind)
    | exact superpose eq214896 eq215935
    | exact resolve eq215935 eq214896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214896 eq215935
  have eq216824 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq216823
  have eq216825 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq216824
  have eq217083 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq216825
       grind)
    | exact superpose eq216825 eq10
    | exact resolve eq10 eq216825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216825
  have eq217362 : x = y ∨ x = y := by
    first
    | (have i₁ := eq217083
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq217083
    | exact resolve eq217083 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217083
  have eq217363 : x = y := by grind
  clear eq217362
  have eq217889 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq217363
       grind)
    | exact superpose eq217363 eq16
    | exact resolve eq16 eq217363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217363
  have eq217890 : False := by grind
  exact eq217890

/-- `Equation3284`: `x ◇ x = y ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_y_pyx_Equation3284 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3284 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3284.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
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
  have eq27 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X2
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq35 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq31
    | exact resolve eq31 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq35
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (M.op X1 (M.op X1 X0)) = X0 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq74 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq27 (σ X0) (σ X0) x
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq27
    | exact resolve eq27 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq27 X1 x X3
       have i₂ := eq27 X1 x X0
       grind)
    | (have i₁ := eq27 X0 X0 x
       have i₂ := eq27 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq27 eq27
    | exact resolve eq27 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq105 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq22 (M.op X0 X0)
       grind)
    | exact superpose eq22 eq74
    | exact resolve eq74 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq183 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op X0 (M.op X0 (M.op X1 (τ X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 X2
       have i₂ := eq9 (τ X2) X0 X1
       grind)
    | exact superpose eq9 eq36
    | exact resolve eq36 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1076 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq59 X1 X0
       grind)
    | exact superpose eq59 eq10
    | (have j1 := eq59 X1 X0
       grind)
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1088 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1076 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1076
    | (have j0 := eq1076 X0 X1
       grind)
    | exact resolve eq1076 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1567 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (σ (M.op X0 (M.op X0 (M.op X1 (τ (σ X2)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2
       have i₂ := eq183 X0 X1 (σ X2)
       grind)
    | exact superpose eq183 eq22
    | exact resolve eq22 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1582 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (σ (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1567 X0 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq1567
    | exact resolve eq1567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq3621 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (M.op X2 X0) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq105 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq105
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq105 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq3865 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X2 X0) = (k X0 X2) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1582 X1 X1 X0
       have i₂ := eq56 X0 X1 X2
       grind)
    | exact superpose eq56 eq1582
    | (have j1 := eq56 X0 X1 X2
       grind)
    | exact resolve eq1582 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1582
  have eq28117 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1088 y x
       grind)
    | exact superpose eq1088 eq16
    | (have j1 := eq1088 y x
       grind)
    | exact resolve eq16 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088
  have eq254019 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq3621 y (σ x) X0
       grind)
    | exact superpose eq3621 eq16
    | (have j1 := eq3621 y x X0
       grind)
    | (have r₁ := eq16
       have r₂ := eq3621 (σ (M.op x y)) x (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq3621 (M.op (σ x) (σ y)) x (σ (M.op x y))
       grind)
    | exact resolve eq16 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621
  have eq254024 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq254019 X0
       have j1 := eq3865 y x X0
       grind)
    | (have r₁ := eq254019 X0
       have r₂ := eq3865 y x x
       grind)
    | (have r₁ := eq254019 X0
       have r₂ := eq3865 (σ (M.op x y)) x (σ (M.op y y))
       grind)
    | (have r₁ := eq254019 X0
       have r₂ := eq3865 (σ (M.op y y)) x (σ (M.op x y))
       grind)
    | exact resolve eq254019 eq3865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865 eq254019
  have eq254036 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq19 X0 y
       have i₂ := eq254024 (τ X0)
       grind)
    | exact superpose eq254024 eq19
    | (have j1 := eq254024 (τ X0)
       grind)
    | exact resolve eq19 eq254024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq255625 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ y) (σ X0)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq254036 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq254036
    | exact resolve eq254036 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254036
  have eq255653 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq255625 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq255625
    | (have j0 := eq255625 X0
       grind)
    | exact resolve eq255625 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255625
  have eq260267 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28117
       have i₂ := eq255653 x
       grind)
    | exact superpose eq255653 eq28117
    | (have j1 := eq255653 (M.op y y)
       grind)
    | (have r₁ := eq28117
       have r₂ := eq255653 x
       grind)
    | exact resolve eq28117 eq255653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28117 eq255653
  have eq260268 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq260267
  have eq260273 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq260268
       grind)
    | exact superpose eq260268 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq260268
       grind)
    | exact resolve eq13 eq260268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260278 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 y x
       have i₂ := eq260268
       grind)
    | exact superpose eq260268 eq76
    | exact resolve eq76 eq260268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq260469 : ∀ X0 : G, (k y X0) = X0 ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq260273 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260273
  have eq260834 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq260268
       have i₂ := eq260278 X0 y
       grind)
    | (have i₁ := eq260268
       have i₂ := eq260278 y X0
       grind)
    | exact superpose eq260278 eq260268
    | exact resolve eq260268 eq260278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260268 eq260278
  have eq260835 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq260834 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260834
  have eq262911 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq254024 X0
       have i₂ := eq260469 X0
       grind)
    | exact superpose eq260469 eq254024
    | (have j0 := eq254024 X0
       have j1 := eq260469 X0
       grind)
    | exact resolve eq254024 eq260469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254024 eq260469
  have eq262922 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq262911 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262911
  have eq263279 : ∀ X0 : G, y = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ y = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq260835 X0
       have i₂ := eq262922 X0
       grind)
    | exact superpose eq262922 eq260835
    | (have j1 := eq262922 X0
       grind)
    | exact resolve eq260835 eq262922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260835 eq262922
  have eq263304 : ∀ X0 : G, (σ x) = (σ y) ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have j0 := eq263279 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263279
  have eq263406 : ∀ X0 : G, y = (τ (σ x)) ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq263304 X0
       grind)
    | exact superpose eq263304 eq10
    | (have j1 := eq263304 (τ (σ x))
       grind)
    | exact resolve eq10 eq263304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263304
  have eq265133 : ∀ X0 : G, x = y ∨ y = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq263406 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq263406
    | (have j0 := eq263406 x
       grind)
    | exact resolve eq263406 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263406
  have eq265134 : ∀ X0 : G, x = y ∨ y = X0 := by
    intro X0
    first
    | (have j0 := eq265133 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265133
  have eq266281 : y ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq265134 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq265134 eq16
    | (have j1 := eq265134 x
       grind)
    | exact resolve eq16 eq265134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267078 : x = y := by
    first
    | (have j1 := eq265134 x
       grind)
    | (have r₁ := eq266281
       have r₂ := eq265134 (σ (M.op x y))
       grind)
    | exact resolve eq266281 eq265134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265134 eq266281
  have eq267193 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq267078
       grind)
    | exact superpose eq267078 eq16
    | exact resolve eq16 eq267078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267078
  have eq267232 : False := by grind
  exact eq267232

/-- `Equation3309`: `x ◇ y = x ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pxy_Equation3309 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3309 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3309.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq66 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq81 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq101 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq81 (σ X1) (σ X0)
       grind)
    | exact superpose eq81 eq15
    | (have j1 := eq81 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq81 X1 (τ X0)
       grind)
    | exact superpose eq81 eq19
    | (have j1 := eq81 X1 (τ X0)
       grind)
    | exact resolve eq19 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq110 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq81
  have eq131 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq132 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq131 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq150 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq132 (σ X0)
       grind)
    | exact superpose eq132 eq15
    | exact resolve eq15 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq150 X0
       have i₂ := eq132 X0
       grind)
    | exact superpose eq132 eq150
    | exact resolve eq150 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq150
  have eq251 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq161 X0
       grind)
    | exact superpose eq161 eq9
    | exact resolve eq9 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq262 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq254 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq254
    | exact resolve eq254 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq265 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq262
  have eq617 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq251 X0 (σ (M.op X0 X0))
       have i₂ := eq161 (M.op X0 X0)
       grind)
    | exact superpose eq161 eq251
    | exact resolve eq251 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq650 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq617 X0
       have i₂ := eq265 (M.op X0 X0)
       grind)
    | exact superpose eq265 eq617
    | exact resolve eq617 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq617
  have eq656 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq650 X0
       have i₂ := eq9 (M.op X0 X0) X0
       grind)
    | exact superpose eq9 eq650
    | exact resolve eq650 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq2878 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq103
    | exact resolve eq103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3011 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2878 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2878
    | (have j0 := eq2878 X0 X1
       grind)
    | exact resolve eq2878 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2878
  have eq4690 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq101 X1 X0
       grind)
    | exact superpose eq101 eq10
    | (have j1 := eq101 X1 X0
       grind)
    | exact resolve eq10 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq4840 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4690 X0 X1
       have i₂ := eq161 X0
       grind)
    | exact superpose eq161 eq4690
    | (have j0 := eq4690 X0 X1
       grind)
    | exact resolve eq4690 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq4690
  have eq4957 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4840 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4840
    | (have j0 := eq4840 X0 X1
       grind)
    | exact resolve eq4840 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4840
  have eq5226 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4957 y x
       grind)
    | exact superpose eq4957 eq16
    | (have j1 := eq4957 y x
       grind)
    | exact resolve eq16 eq4957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957
  have eq5318 : x = (M.op y y) := by
    first
    | (have j1 := eq3011 x y
       grind)
    | (have r₁ := eq5226
       have r₂ := eq3011 x y
       grind)
    | exact resolve eq5226 eq3011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3011 eq5226
  have eq5652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq656 y
       have i₂ := eq5318
       grind)
    | exact superpose eq5318 eq656
    | exact resolve eq656 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656 eq5318
  have eq5664 : False := by grind
  exact eq5664

/-- `Equation3309`: `x ◇ y = x ◇ (x ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3309 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3309 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3309.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq92 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46 x y
       grind)
    | exact superpose eq46 eq16
    | (have j1 := eq46 x y
       grind)
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq309 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq335 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq309 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq309
    | (have j0 := eq309 X0 X1
       grind)
    | exact resolve eq309 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq774 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq92
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq92
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq92
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq92 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq775 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq774
  have eq3663 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq775
       grind)
    | exact superpose eq775 eq16
    | exact resolve eq16 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3666 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq775
       grind)
    | exact superpose eq775 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq775
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq775
       grind)
    | exact resolve eq13 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq3667 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3666
  have eq3668 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq3667
  have eq3672 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3668
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3668
    | exact resolve eq3668 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3668
  have eq6102 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq335 y x
       have i₂ := eq3672
       grind)
    | exact superpose eq3672 eq335
    | (have j0 := eq335 y x
       grind)
    | exact resolve eq335 eq3672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq3672
  have eq6139 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6102
  have eq6163 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6139
       have r₂ := eq3663
       grind)
    | exact resolve eq6139 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663 eq6139
  have eq6297 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq6163
       grind)
    | exact superpose eq6163 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq6163
       grind)
    | exact resolve eq13 eq6163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6298 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq6297
  have eq6299 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq6298
  have eq6435 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq95 x y
       have i₂ := eq6299
       grind)
    | exact superpose eq6299 eq95
    | (have j0 := eq95 x y
       grind)
    | exact resolve eq95 eq6299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq6299
  have eq6438 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6435
  have eq6439 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6438
  have eq6611 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq6439
       grind)
    | exact superpose eq6439 eq16
    | exact resolve eq16 eq6439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6439
  have eq6796 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6611
       have i₂ := eq6163
       grind)
    | exact superpose eq6163 eq6611
    | exact resolve eq6611 eq6163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163 eq6611
  have eq6797 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq6796
  have eq6798 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq6797
  have eq6948 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6798
       grind)
    | exact superpose eq6798 eq10
    | exact resolve eq10 eq6798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6798
  have eq7016 : x = y ∨ x = y := by
    first
    | (have i₁ := eq6948
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6948
    | exact resolve eq6948 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6948
  have eq7017 : x = y := by grind
  clear eq7016
  have eq7163 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7017
       grind)
    | exact superpose eq7017 eq16
    | exact resolve eq16 eq7017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7017
  have eq7164 : False := by grind
  exact eq7164

/-- `Equation3317`: `x ◇ y = x ◇ (y ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation3317 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3317 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3317.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 (M.op X1 X0)
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq26
    | exact resolve eq26 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq42
    | (have j0 := eq42 X0 X1
       grind)
    | exact resolve eq42 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq54 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq68 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq26
    | exact resolve eq26 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq50 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq50 X0 X1
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X0 X1
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq227 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq215
    | (have j0 := eq215 X0 X1
       grind)
    | exact resolve eq215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq332 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq26
    | exact resolve eq26 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq68
  have eq334 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq332 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq332
    | exact resolve eq332 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq343 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq334 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq334
    | exact resolve eq334 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq334
  have eq1688 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1818 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1688 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1688
    | (have j0 := eq1688 X0 X1
       grind)
    | exact resolve eq1688 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688
  have eq2706 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq227 x y
       grind)
    | exact superpose eq227 eq16
    | (have j1 := eq227 x y
       grind)
    | exact resolve eq16 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq45171 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2706
       have i₂ := eq1818 x y
       grind)
    | exact superpose eq1818 eq2706
    | (have j1 := eq1818 x y
       grind)
    | (have r₁ := eq2706
       have r₂ := eq1818 x y
       grind)
    | (have r₁ := eq2706
       have r₂ := eq1818 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2706
       have r₂ := eq1818 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2706 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818 eq2706
  have eq45190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45171
  have eq45191 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45190
  have eq45226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq343 y
       have i₂ := eq45191
       grind)
    | exact superpose eq45191 eq343
    | exact resolve eq343 eq45191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq45191
  have eq45350 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq45226
       have r₂ := eq16
       grind)
    | exact resolve eq45226 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45226
  have eq45667 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq45350
       grind)
    | exact superpose eq45350 eq10
    | exact resolve eq10 eq45350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45350
  have eq45757 : x = y ∨ x = y := by
    first
    | (have i₁ := eq45667
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq45667
    | exact resolve eq45667 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45667
  have eq45758 : x = y := by grind
  clear eq45757
  have eq46655 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq45758
       grind)
    | exact superpose eq45758 eq16
    | exact resolve eq16 eq45758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45758
  have eq46656 : False := by grind
  exact eq46656

/-- `Equation3317`: `x ◇ y = x ◇ (y ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation3317 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3317 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3317.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X1 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 (M.op X1 X0)
       have i₂ := eq26 X1 X0
       grind)
    | exact superpose eq26 eq26
    | exact resolve eq26 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq41 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq41
    | (have j0 := eq41 X0 X1
       grind)
    | exact resolve eq41 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq53 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq67 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq26
    | exact resolve eq26 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq49 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq49 X0 X1
       grind)
    | exact superpose eq49 eq10
    | (have j1 := eq49 X0 X1
       grind)
    | exact resolve eq10 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq224 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq212
    | (have j0 := eq212 X0 X1
       grind)
    | exact resolve eq212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq329 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq26
    | exact resolve eq26 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq67
  have eq331 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq329 X0
       have i₂ := eq23 (M.op X0 X0)
       grind)
    | exact superpose eq23 eq329
    | exact resolve eq329 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq340 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq331 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq331
    | exact resolve eq331 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq331
  have eq1542 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1670 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1542 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1542
    | (have j0 := eq1542 X0 X1
       grind)
    | exact resolve eq1542 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq2412 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq224 x y
       grind)
    | exact superpose eq224 eq16
    | (have j1 := eq224 x y
       grind)
    | exact resolve eq16 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq38854 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2412
       have i₂ := eq1670 x y
       grind)
    | exact superpose eq1670 eq2412
    | (have j1 := eq1670 x y
       grind)
    | (have r₁ := eq2412
       have r₂ := eq1670 x y
       grind)
    | (have r₁ := eq2412
       have r₂ := eq1670 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2412
       have r₂ := eq1670 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2412 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670 eq2412
  have eq38870 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38854
  have eq38871 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq38870
  have eq40420 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq340 y
       have i₂ := eq38871
       grind)
    | exact superpose eq38871 eq340
    | exact resolve eq340 eq38871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq38871
  have eq40524 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq40420
       have r₂ := eq16
       grind)
    | exact resolve eq40420 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40420
  have eq42256 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq40524
       grind)
    | exact superpose eq40524 eq10
    | exact resolve eq10 eq40524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40524
  have eq42347 : x = y ∨ x = y := by
    first
    | (have i₁ := eq42256
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq42256
    | exact resolve eq42256 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42256
  have eq42348 : x = y := by grind
  clear eq42347
  have eq42657 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq42348
       grind)
    | exact superpose eq42348 eq16
    | exact resolve eq16 eq42348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42348
  have eq42658 : False := by grind
  exact eq42658

/-- `Equation3317`: `x ◇ y = x ◇ (y ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3317 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3317 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3317.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq44 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq96 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq40 x y
       grind)
    | exact superpose eq40 eq16
    | (have j1 := eq40 x y
       grind)
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq708 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44
    | exact resolve eq44 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq751 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq708
    | (have j0 := eq708 X0 X1
       grind)
    | exact resolve eq708 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq1212 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq96
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq96
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq96
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq96
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq96 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1213 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1212
  have eq10881 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq16
    | exact resolve eq16 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10883 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1213
       grind)
    | exact superpose eq1213 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1213
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1213
       grind)
    | exact resolve eq13 eq1213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq10908 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10883
  have eq10909 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq10908
  have eq10914 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10909
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq10909
    | exact resolve eq10909 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10909
  have eq17354 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq751 y x
       have i₂ := eq10914
       grind)
    | exact superpose eq10914 eq751
    | (have j0 := eq751 y x
       grind)
    | exact resolve eq751 eq10914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq10914
  have eq17417 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17354
  have eq17447 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17417
       have r₂ := eq10881
       grind)
    | exact resolve eq17417 eq10881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10881 eq17417
  have eq17684 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq17447
       grind)
    | exact superpose eq17447 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17447
       grind)
    | exact resolve eq13 eq17447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17715 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq17684
  have eq17716 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq17715
  have eq17953 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq101 x y
       have i₂ := eq17716
       grind)
    | exact superpose eq17716 eq101
    | (have j0 := eq101 x y
       grind)
    | exact resolve eq101 eq17716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq17716
  have eq17963 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17953
  have eq17964 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17963
  have eq18275 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq17964
       grind)
    | exact superpose eq17964 eq16
    | exact resolve eq16 eq17964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17964
  have eq18645 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18275
       have i₂ := eq17447
       grind)
    | exact superpose eq17447 eq18275
    | exact resolve eq18275 eq17447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17447 eq18275
  have eq18646 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18645
  have eq18647 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq18646
  have eq18750 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18647
       grind)
    | exact superpose eq18647 eq10
    | exact resolve eq10 eq18647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18647
  have eq18845 : x = y ∨ x = y := by
    first
    | (have i₁ := eq18750
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18750
    | exact resolve eq18750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18750
  have eq18846 : x = y := by grind
  clear eq18845
  have eq19155 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18846
       grind)
    | exact superpose eq18846 eq16
    | exact resolve eq16 eq18846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18846
  have eq19156 : False := by grind
  exact eq19156

/-- `Equation3321`: `x ◇ y = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxx_y_pxy_Equation3321 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3321 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3321.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X0 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq23
  have eq43 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) (τ X0))) X0) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq46 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43
    | (have j0 := eq43 X0
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq61 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq330 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X1 X1
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq63
    | (have j0 := eq63 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq63 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 X2 : G, (M.op (σ X0) X1) = (M.op (σ X0) (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X2)) = (σ (k X0 X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 (σ X2)
       have i₂ := eq63 X0 X2
       grind)
    | exact superpose eq63 eq9
    | (have j1 := eq63 X0 X2
       grind)
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq63 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq63 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq378 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq377 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq380 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq369 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq330 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq389 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq380 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq380
    | (have j0 := eq380 X0 X1
       grind)
    | exact resolve eq380 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq391 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ X0) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq359 X0 X1
       have i₂ := eq15 X1 X1
       grind)
    | exact superpose eq15 eq359
    | (have j0 := eq359 X0 X1
       grind)
    | exact resolve eq359 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq406 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq391 X0 X1
       have j1 := eq385 X0 X1
       grind)
    | (have r₁ := eq391 X0 (k X1 X1)
       have r₂ := eq385 X0 X1
       grind)
    | (have r₁ := eq391 (k X1 X1) X0
       have r₂ := eq385 X0 X1
       grind)
    | (have r₁ := eq391 X0 X1
       have r₂ := eq385 X0 X1
       grind)
    | exact resolve eq391 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq391
  have eq1712 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61
    | exact resolve eq61 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1785 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1712 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1712
    | (have j0 := eq1712 X0 X1
       grind)
    | exact resolve eq1712 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712
  have eq3586 : ∀ X0 : G, (σ X0) = (k (σ (M.op X0 X0)) (σ X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq46 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46
    | exact resolve eq46 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq3661 : ∀ X0 : G, (σ X0) = (σ (k (M.op X0 X0) X0)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3586 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq3586
    | (have j0 := eq3586 X0
       grind)
    | exact resolve eq3586 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3586
  have eq3695 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3661 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq3661 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq3661
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq3661 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq3745 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3695 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3695
  have eq5427 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq378 X0
       have i₂ := eq3745 X0 X0
       grind)
    | exact superpose eq3745 eq378
    | (have j0 := eq378 X0
       have j1 := eq3745 X0 X0
       grind)
    | (have r₁ := eq378 X0
       have r₂ := eq3745 X0 X0
       grind)
    | exact resolve eq378 eq3745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378 eq3745
  have eq5459 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5427 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5427
  have eq5479 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5459 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq5459 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq5459 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq5459 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5459
  have eq5652 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq5479 X0
       grind)
    | exact superpose eq5479 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq5479 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq5479 X0
       grind)
    | exact resolve eq12 eq5479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5479
  have eq5691 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5652 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5652
  have eq5696 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq5691 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq5691
    | (have j0 := eq5691 X0
       grind)
    | exact resolve eq5691 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5691
  have eq6110 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1785 X0 X0
       have i₂ := eq5696 X0
       grind)
    | exact superpose eq5696 eq1785
    | (have j0 := eq1785 X0 X0
       have j1 := eq5696 X0
       grind)
    | exact resolve eq1785 eq5696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785 eq5696
  have eq6145 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6110 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6110
  have eq6167 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq6145 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq6145 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq6145 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6145
  have eq7171 : ∀ X0 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq6167 X0
       grind)
    | exact superpose eq6167 eq10
    | (have j1 := eq6167 X0
       grind)
    | exact resolve eq10 eq6167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6167
  have eq7231 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq7171 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7171
    | (have j0 := eq7171 X0
       grind)
    | exact resolve eq7171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7171
  have eq7241 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7231 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq7231 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq7231 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7231
  have eq7575 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7241 (σ X0)
       grind)
    | exact superpose eq7241 eq15
    | exact resolve eq15 eq7241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7581 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq7241 (τ X0)
       grind)
    | exact superpose eq7241 eq35
    | exact resolve eq35 eq7241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7588 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7581 X0
       have i₂ := eq7241 X0
       grind)
    | exact superpose eq7241 eq7581
    | exact resolve eq7581 eq7241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7581
  have eq7594 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7575 X0
       have i₂ := eq7241 X0
       grind)
    | exact superpose eq7241 eq7575
    | exact resolve eq7575 eq7241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7575
  have eq7944 : ∀ X0 X1 : G, (M.op (M.op X1 (τ X0)) (τ X0)) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (τ X0) (τ X0) X1
       have i₂ := eq7588 X0
       grind)
    | exact superpose eq7588 eq25
    | exact resolve eq25 eq7588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8302 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq389 (τ X1) (τ X0)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq389
    | (have j0 := eq389 (τ (k X0 X1)) (τ X0)
       grind)
    | exact resolve eq389 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq8401 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = X0 ∨ (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq389 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq389
    | exact resolve eq389 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8447 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq389 X0 X1
       grind)
    | exact superpose eq389 eq10
    | (have j1 := eq389 X0 X1
       grind)
    | exact resolve eq10 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq9042 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8447 X0 X1
       have i₂ := eq7594 X0
       grind)
    | exact superpose eq7594 eq8447
    | (have j0 := eq8447 X0 X1
       grind)
    | exact resolve eq8447 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8447
  have eq9081 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = X0 ∨ (M.op X0 X0) = (σ (k (τ X0) X1)) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8401 X0 X1
       have i₂ := eq7594 X1
       grind)
    | exact superpose eq7594 eq8401
    | (have j0 := eq8401 X0 X1
       grind)
    | exact resolve eq8401 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8401
  have eq9166 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8302 X0 X1
       have i₂ := eq7594 (τ X0)
       grind)
    | exact superpose eq7594 eq8302
    | (have j0 := eq8302 X0 X1
       grind)
    | exact resolve eq8302 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8302
  have eq9344 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9042 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq9042
    | (have j0 := eq9042 X0 X1
       grind)
    | exact resolve eq9042 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9042
  have eq9371 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9081 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9081
    | (have j0 := eq9081 X0 X1
       grind)
    | exact resolve eq9081 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9081
  have eq9433 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9166 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9166
    | (have j0 := eq9166 X0 X1
       grind)
    | exact resolve eq9166 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9166
  have eq9550 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9344 X0 X1
       have i₂ := eq7594 X1
       grind)
    | exact superpose eq7594 eq9344
    | (have j0 := eq9344 X0 X1
       grind)
    | exact resolve eq9344 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9344
  have eq9563 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9371 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9371
    | (have j0 := eq9371 X0 X1
       grind)
    | exact resolve eq9371 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq9371
  have eq9600 : ∀ X0 X1 : G, (k X0 X1) = (σ (τ (M.op X0 X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9433 X0 X1
       have i₂ := eq7588 X0
       grind)
    | exact superpose eq7588 eq9433
    | (have j0 := eq9433 X0 X1
       grind)
    | exact resolve eq9433 eq7588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9433
  have eq9690 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9600 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq9600
    | (have j0 := eq9600 X0 X1
       grind)
    | exact resolve eq9600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9600
  have eq9751 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9690 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq9690
    | (have j0 := eq9690 X0 X1
       grind)
    | exact resolve eq9690 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9690
  have eq9767 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9751 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9751
    | (have j0 := eq9751 X0 X1
       grind)
    | exact resolve eq9751 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9751
  have eq9771 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9767 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq9767
    | (have j0 := eq9767 X0 X1
       grind)
    | exact resolve eq9767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9767
  have eq9773 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9771 X0 X1
       have i₂ := eq7594 (τ X1)
       grind)
    | exact superpose eq7594 eq9771
    | (have j0 := eq9771 X0 X1
       grind)
    | exact resolve eq9771 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9771
  have eq9775 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (τ (M.op X1 X1))) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9773 X0 X1
       have i₂ := eq7588 X1
       grind)
    | exact superpose eq7588 eq9773
    | (have j0 := eq9773 X0 X1
       grind)
    | exact resolve eq9773 eq7588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9773
  have eq9776 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9775 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq9775
    | (have j0 := eq9775 X0 X1
       grind)
    | exact resolve eq9775 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9775
  have eq9777 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9776 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq9776
    | (have j0 := eq9776 X0 X1
       grind)
    | exact resolve eq9776 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9776
  have eq14155 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X0 X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368 X0 (σ X1) X2
       have i₂ := eq406 X0 X1
       grind)
    | exact superpose eq406 eq368
    | (have j0 := eq368 X0 X1 X2
       have j1 := eq406 X0 X1
       grind)
    | exact resolve eq368 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq406
  have eq14837 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X0 X2)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14155 X0 X1 X2
       have i₂ := eq7594 X0
       grind)
    | exact superpose eq7594 eq14155
    | (have j0 := eq14155 X0 X1 X2
       grind)
    | exact resolve eq14155 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14155
  have eq14981 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X2 X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X0 X2)) ∨ (σ X0) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14837 X0 X1 X2
       have i₂ := eq7594 X2
       grind)
    | exact superpose eq7594 eq14837
    | (have j0 := eq14837 X0 X1 X2
       grind)
    | exact resolve eq14837 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14837
  have eq15056 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X2 X2)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X2)) = (σ (k X0 X2)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14981 X0 X1 X2
       have i₂ := eq7241 X1
       grind)
    | exact superpose eq7241 eq14981
    | (have j0 := eq14981 X0 X1 X1
       grind)
    | exact resolve eq14981 eq7241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7241 eq14981
  have eq28494 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq7944 X0 (τ X0)
       have i₂ := eq7588 X0
       grind)
    | exact superpose eq7588 eq7944
    | exact resolve eq7944 eq7588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7944
  have eq28686 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq28494 X0
       have i₂ := eq7588 (M.op X0 X0)
       grind)
    | exact superpose eq7588 eq28494
    | exact resolve eq28494 eq7588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7588 eq28494
  have eq28719 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq28686 X0
       have i₂ := eq25 X0 X0 X0
       grind)
    | exact superpose eq25 eq28686
    | exact resolve eq28686 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28686
  have eq29115 : ∀ X0 : G, (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) = (M.op (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq28719 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq28719
    | exact resolve eq28719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28719
  have eq29234 : ∀ X0 : G, (τ (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op (τ (σ (M.op X0 X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq29115 X0
       have i₂ := eq7594 X0
       grind)
    | exact superpose eq7594 eq29115
    | exact resolve eq29115 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29115
  have eq29289 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29234 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq29234
    | exact resolve eq29234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29234
  have eq29888 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ (M.op X0 X0)) (σ X0))
       have i₂ := eq29289 X0
       grind)
    | exact superpose eq29289 eq11
    | exact resolve eq11 eq29289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29289
  have eq30893 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29888 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq29888 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq29888
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq29888 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96476 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq9777 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9777
  have eq133876 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq9563 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9563
  have eq134459 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq9550 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq9550 X0 X1
       grind)
    | exact superpose eq9550 eq10
    | (have j1 := eq9550 X0 X1
       grind)
    | exact resolve eq10 eq9550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9550
  have eq134539 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq134459 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq134459
    | (have j0 := eq134459 X0 X1
       grind)
    | exact resolve eq134459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134459
  have eq165788 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq134539 x y
       grind)
    | exact superpose eq134539 eq16
    | (have j1 := eq134539 x y
       grind)
    | exact resolve eq16 eq134539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134539
  have eq180199 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30893 x y
       grind)
    | exact superpose eq30893 eq16
    | (have j1 := eq30893 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq30893 x y
       grind)
    | exact resolve eq16 eq30893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30893
  have eq180223 : (M.op x y) = (k x y) ∨ x = (M.op y x) := by grind
  clear eq180199
  have eq180232 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq165788
       have i₂ := eq180223
       grind)
    | exact superpose eq180223 eq165788
    | exact resolve eq165788 eq180223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165788 eq180223
  have eq180237 : x = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq180232
  have eq180329 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq29888 y
       have i₂ := eq180237
       grind)
    | exact superpose eq180237 eq29888
    | exact resolve eq29888 eq180237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180237
  have eq180567 : x = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq180329
       have r₂ := eq16
       grind)
    | exact resolve eq180329 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180329
  have eq180581 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 x)) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 x X0 y
       have i₂ := eq180567
       grind)
    | exact superpose eq180567 eq9
    | exact resolve eq9 eq180567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180779 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq180581 y
       have i₂ := eq180567
       grind)
    | exact superpose eq180567 eq180581
    | exact resolve eq180581 eq180567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180567 eq180581
  have eq180913 : (M.op x y) = (M.op x x) := by grind
  clear eq180779
  have eq181095 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq96476 x y
       have i₂ := eq180913
       grind)
    | exact superpose eq180913 eq96476
    | (have j0 := eq96476 x x
       grind)
    | (have r₁ := eq96476 x y
       have r₂ := eq180913
       grind)
    | exact resolve eq96476 eq180913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96476
  have eq181127 : (k x y) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq181095
  have eq233232 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133876 (σ X0) X1
       have i₂ := eq7594 X0
       grind)
    | exact superpose eq7594 eq133876
    | (have j0 := eq133876 (σ X0) X1
       grind)
    | exact resolve eq133876 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7594 eq133876
  have eq233240 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq233232 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq233232
    | (have j0 := eq233232 X0 X1
       grind)
    | exact resolve eq233232 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233232
  have eq237257 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq15056 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15056
  have eq237258 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq237257 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237257
  have eq237259 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq237258 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237258
  have eq237268 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq237259 X0 X1
       have j1 := eq233240 X0 X1
       grind)
    | (have r₁ := eq237259 X0 X1
       have r₂ := eq233240 X0 X1
       grind)
    | exact resolve eq237259 eq233240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233240 eq237259
  have eq237371 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq237268 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq237268 X0 X1
       grind)
    | exact superpose eq237268 eq10
    | (have j1 := eq237268 X0 X1
       grind)
    | exact resolve eq10 eq237268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237268
  have eq237507 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq237371 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq237371
    | (have j0 := eq237371 X0 X1
       grind)
    | exact resolve eq237371 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237371
  have eq238051 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq237507 x y
       grind)
    | exact superpose eq237507 eq16
    | (have j1 := eq237507 x y
       grind)
    | exact resolve eq16 eq237507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237507
  have eq238263 : (σ (k x y)) ≠ (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq238051
       have i₂ := eq180913
       grind)
    | exact superpose eq180913 eq238051
    | exact resolve eq238051 eq180913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180913 eq238051
  have eq238461 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq238263
       have i₂ := eq181127
       grind)
    | exact superpose eq181127 eq238263
    | exact resolve eq238263 eq181127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181127 eq238263
  have eq238488 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op y y) := by grind
  clear eq238461
  have eq238489 : x = (M.op y y) := by grind
  clear eq238488
  have eq238794 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29888 y
       have i₂ := eq238489
       grind)
    | exact superpose eq238489 eq29888
    | exact resolve eq29888 eq238489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29888 eq238489
  have eq239424 : False := by grind
  exact eq239424
