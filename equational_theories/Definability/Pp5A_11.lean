import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_x_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = a :=
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
  have eq95 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
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
  have eq100 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq100 (σ X0) (σ X1)
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq145 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X0 X1
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq109
    | (have j0 := eq109 X0 X1
       have j1 := eq100 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq109 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq109
  have eq317 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1
       have i₂ := eq95 X0 (σ X1)
       grind)
    | (have i₁ := eq22 X1
       have i₂ := eq95 (σ X1) X0
       grind)
    | exact superpose eq95 eq22
    | exact resolve eq22 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq95
  have eq2044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq145 x y
       grind)
    | exact superpose eq145 eq16
    | (have j1 := eq145 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq145 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq2057 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2044
  have eq7787 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2057
       grind)
    | exact superpose eq2057 eq10
    | exact resolve eq10 eq2057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057
  have eq7800 : x = y ∨ x = y := by
    first
    | (have i₁ := eq7787
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7787
    | exact resolve eq7787 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7787
  have eq7801 : x = y := by grind
  clear eq7800
  have eq17741 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7801
       grind)
    | exact superpose eq7801 eq16
    | exact resolve eq16 eq7801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7801
  have eq17742 : False := by grind
  exact eq17742

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_x_y_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq29 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq15
    | (have j0 := eq15 X0 (M.op x y)
       grind)
    | exact resolve eq15 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : x = (τ (σ x)) := by
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
  have eq44 : y = (τ (σ y)) := by
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
  have eq55 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq56 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq32 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32
    | (have j0 := eq32 y
       grind)
    | exact resolve eq32 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq100 : ∀ X0 X1 : G, (k (σ (σ X0)) X1) = (σ (σ (k X0 (τ (τ X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 (σ X0)
       have i₂ := eq55 (τ X1) X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) (τ X2))) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 (k X0 (τ X1))
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq10
    | exact resolve eq10 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) (M.op x y))) = (k (k (σ X0) X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (k X0 (τ X1))
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq31
    | exact resolve eq31 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq129 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq107 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq107
    | exact resolve eq107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq227 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq60 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X2
       have i₂ := eq227 X0 X2
       grind)
    | (have i₁ := eq9 X2 X1 X2
       have i₂ := eq227 X2 X0
       grind)
    | exact superpose eq227 eq9
    | exact resolve eq9 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq227 X2 (M.op X1 (M.op X0 X0))
       grind)
    | (have i₁ := eq60 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq227 (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact superpose eq227 eq60
    | exact resolve eq60 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq254 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X1 X1)
       have i₂ := eq227 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq9 X2 X1 (M.op X1 X1)
       have i₂ := eq227 (M.op X1 X1) X0
       grind)
    | exact superpose eq227 eq9
    | exact resolve eq9 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X0 (M.op X1 (M.op X2 X2))) = X1 ∨ (k (M.op X0 (M.op X1 (M.op X2 X2))) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 (M.op X1 (M.op X2 X2))) X1
       have i₂ := eq60 X1 X2 X0
       grind)
    | exact superpose eq60 eq13
    | (have j0 := eq13 (M.op X0 (M.op X1 (M.op X2 X2))) X1
       grind)
    | (have r₁ := eq13 (M.op X2 (M.op X2 (M.op X1 X1))) X2
       have r₂ := eq60 X2 X1 X2
       grind)
    | exact resolve eq13 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : x ≠ (M.op x y) ∨ x = y ∨ x = (k y x) := by
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
  have eq260 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq73 eq260
    | exact resolve eq260 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq283 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq56
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq73
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq293 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq291
    | exact resolve eq291 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq295 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq293
    | exact resolve eq293 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq372 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq250 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq250 eq60
    | exact resolve eq60 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq646 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq295
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq295
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq295 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq656 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq646
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq646
    | exact resolve eq646 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq656
    | exact resolve eq656 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq658 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq657
       have r₂ := eq28
       grind)
    | exact resolve eq657 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq659 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq658
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq658
    | exact resolve eq658 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq660 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq659 eq261
    | (have r₁ := eq261
       have r₂ := eq659
       grind)
    | exact resolve eq261 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq662 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq659 eq28
    | exact resolve eq28 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq663 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq660
  have eq664 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq663
  have eq665 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq664
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq664
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq664 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq679 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq665
  have eq689 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq679
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq679
    | exact resolve eq679 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679
  have eq691 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq689
    | exact resolve eq689 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq692 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq691
       have r₂ := eq662
       grind)
    | exact resolve eq691 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662 eq691
  have eq693 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq692
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq692
    | exact resolve eq692 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq694 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq693
  have eq699 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq694 eq44
    | exact resolve eq44 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq707 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq43 eq699
    | exact resolve eq699 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq708 : x = (M.op x y) ∨ x = y := by grind
  clear eq707
  have eq712 : x ≠ x ∨ x = y ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq708 eq259
    | (have r₁ := eq259
       have r₂ := eq708
       grind)
    | exact resolve eq259 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq714 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq708 eq21
    | exact resolve eq21 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708
  have eq715 : x ≠ x ∨ x = y ∨ x = (k y x) := by grind
  clear eq712
  have eq716 : x = (k y x) ∨ x = y := by grind
  clear eq715
  have eq717 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq714
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq714
    | exact resolve eq714 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq768 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq60 X2 X3 X0
       grind)
    | exact superpose eq60 eq62
    | exact resolve eq62 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq836 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) (M.op X3 X1)) = (M.op (M.op (M.op X2 X2) X3) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X4 X4) (M.op X3 X1)) X2 X3
       have i₂ := eq62 X3 X4 X1 X0
       grind)
    | (have i₁ := eq9 (M.op X3 X3) X1 X2
       have i₂ := eq62 X0 X1 X2 X3
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq918 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq295
       have i₂ := eq716
       grind)
    | exact superpose eq716 eq295
    | exact resolve eq295 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq716
  have eq928 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq918
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq918
    | exact resolve eq918 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq929 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq928
  have eq1048 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq929 eq28
    | exact resolve eq28 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq1051 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1048
       have r₂ := eq717
       grind)
    | exact resolve eq1048 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq1048
  have eq1056 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1051 eq44
    | exact resolve eq44 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1051
  have eq1066 : x = y ∨ x = y := by
    first
    | exact superpose eq43 eq1056
    | exact resolve eq1056 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1056
  have eq1067 : x = y := by grind
  clear eq1066
  have eq1071 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1067
       grind)
    | exact superpose eq1067 eq19
    | exact resolve eq19 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1072 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1067
       grind)
    | exact superpose eq1067 eq25
    | exact resolve eq25 eq1067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1067
  have eq1130 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1072
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1072
    | exact resolve eq1072 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1072
  have eq1144 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1130 eq27
    | exact resolve eq27 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1130
  have eq1195 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 x X0
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq9
    | exact resolve eq9 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1196 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 x X1
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq60
    | exact resolve eq60 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1199 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq227 x X0
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq227
    | exact resolve eq227 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq1205 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq252 X1 X0 x
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq252
    | exact resolve eq252 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq1206 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq254 X0 x X1
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq254
    | exact resolve eq254 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254
  have eq1209 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq372 X1 X0 x
       have i₂ := eq1071
       grind)
    | exact superpose eq1071 eq372
    | exact resolve eq372 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq1071
  have eq1222 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op x y) X0) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq768 X0 X1 X2 X3 x
       have i₂ := eq1209 x X0
       grind)
    | exact superpose eq1209 eq768
    | exact resolve eq768 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq1227 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X4 X4) (M.op X3 X1)) = (M.op (M.op (M.op X2 X2) X3) (M.op (M.op x y) X1)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq836 x X1 X2 X3 X4
       have i₂ := eq1209 x X1
       grind)
    | exact superpose eq1209 eq836
    | exact resolve eq836 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq1258 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq1206 x X1
       have i₂ := eq1209 x (M.op X1 sF0)
       grind)
    | exact superpose eq1209 eq1206
    | exact resolve eq1206 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1206 eq1209
  have eq1261 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op x y))) = X1 ∨ X0 ≠ X1 ∨ (k (M.op X0 (M.op X1 (M.op X2 X2))) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq255 X0 X1 X2
       have i₂ := eq1205 X1 X2
       grind)
    | exact superpose eq1205 eq255
    | (have j0 := eq255 X0 X1 X2
       grind)
    | (have r₁ := eq255 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op x y)) X2
       have r₂ := eq1205 X0 X1
       grind)
    | (have r₁ := eq255 (M.op X0 (M.op x y)) (M.op X0 (M.op X1 X1)) X2
       have r₂ := eq1205 X0 X1
       grind)
    | exact resolve eq255 eq1205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq1205
  have eq1270 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1144
       have i₂ := eq1199 sF2
       grind)
    | exact superpose eq1199 eq1144
    | exact resolve eq1144 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq1297 : ∀ X1 X3 X4 : G, (M.op (M.op X4 X4) (M.op X3 X1)) = (M.op (M.op (M.op x y) X3) (M.op (M.op x y) X1)) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq1227 X1 x X3 X4
       have i₂ := eq1199 x
       grind)
    | exact superpose eq1199 eq1227
    | exact resolve eq1227 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1302 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X2) = (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1222 X0 X1 X2 x
       have i₂ := eq1199 x
       grind)
    | exact superpose eq1199 eq1222
    | exact resolve eq1222 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1222
  have eq1313 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 (M.op X1 (M.op x y))) = X1 ∨ (k (M.op X0 (M.op X1 (M.op x y))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1261 X0 X1 x
       have i₂ := eq1199 x
       grind)
    | exact superpose eq1199 eq1261
    | (have j0 := eq1261 X0 X1 x
       grind)
    | (have r₁ := eq1261 (M.op x y) (M.op X0 X0) x
       have r₂ := eq1199 X0
       grind)
    | (have r₁ := eq1261 (M.op X0 X0) (M.op x y) x
       have r₂ := eq1199 X0
       grind)
    | exact resolve eq1261 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1316 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq1270 eq28
    | exact resolve eq28 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1270
  have eq1343 : ∀ X1 X3 : G, (M.op (M.op (M.op x y) X3) (M.op (M.op x y) X1)) = (M.op (M.op x y) (M.op X3 X1)) := by
    intro X1 X3
    first
    | (have i₁ := eq1297 X1 X3 x
       have i₂ := eq1199 x
       grind)
    | exact superpose eq1199 eq1297
    | exact resolve eq1297 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1348 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) X0) X2) = (M.op (M.op x y) (M.op X0 (M.op X2 (M.op x y)))) := by
    intro X0 X2
    first
    | (have i₁ := eq1302 X0 x X2
       have i₂ := eq1199 x
       grind)
    | exact superpose eq1199 eq1302
    | exact resolve eq1302 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1473 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op X1 X0) (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1348 eq1195
    | exact resolve eq1195 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1527 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 (M.op (M.op X0 X1) (M.op x y))))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq1473 eq1195
    | exact resolve eq1195 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1646 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 (M.op (M.op X0 X1) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1527 X0 X1 (M.op X1 (M.op (M.op X0 X1) sF0))
       have i₂ := eq1199 (M.op X1 (M.op (M.op X0 X1) sF0))
       grind)
    | exact superpose eq1199 eq1527
    | exact resolve eq1527 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527
  have eq1754 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1646 eq1196
    | exact resolve eq1196 eq1646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1829 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op x y))))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1348 eq1754
    | exact resolve eq1754 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1836 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op x y)) = (M.op (M.op X1 (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1754 eq1646
    | exact resolve eq1646 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1844 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1196 eq1829
    | exact resolve eq1829 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq1871 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op x y) X0) X1) X2) (M.op X0 (M.op X1 (M.op x y)))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq1348 eq1844
    | exact resolve eq1844 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2081 : ∀ X0 : G, (k (M.op X0 (M.op X0 (M.op x y))) X0) = X0 ∨ (M.op X0 (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq1313 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq3263 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 (M.op X0 (M.op x y)))) (τ X0)) ∨ (M.op X0 (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq2081 eq148
    | (have j1 := eq2081 X0
       grind)
    | exact resolve eq148 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2081
  have eq9151 : (M.op x y) = (k (τ (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y)))) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq42 eq3263
    | (have j0 := eq3263 (σ (M.op x y))
       grind)
    | exact resolve eq3263 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3263
  have eq10686 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (σ (k X0 (τ (τ (σ X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (σ X0) X1
       have i₂ := eq100 X0 (σ X1)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq10707 : ∀ X0 X1 : G, (σ (k (σ X0) X1)) = (σ (σ (k X0 (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq10686 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq10686
    | exact resolve eq10686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10686
  have eq52964 : ∀ X0 X1 X2 X3 : G, (σ (k (k (k (k X0 (τ X1)) (M.op x y)) (τ X2)) (τ X3))) = (k (k (k (k (σ X0) X1) (σ (M.op x y))) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq112 eq102
    | exact resolve eq102 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52978 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (k (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 (k X0 (τ X1))
       have i₂ := eq102 X0 X1 X2
       grind)
    | exact superpose eq102 eq55
    | exact resolve eq55 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53062 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (k (k (σ X0) X1) (σ (k X0 (τ X1)))) := by
    intro X0 X1
    grind
  have eq53114 : ∀ X0 X1 X2 X3 : G, (k (k (k (σ X0) X1) (σ X2)) X3) = (σ (k (k (k X0 (τ X1)) X2) (τ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X3 (k (k X0 (τ X1)) X2)
       have i₂ := eq108 X0 X1 X2
       grind)
    | exact superpose eq108 eq55
    | exact resolve eq55 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75883 : ∀ X0 X1 X2 : G, (σ (k (k X0 (k X1 (τ X2))) (M.op x y))) = (k (k (σ X0) (k (σ X1) X2)) (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 (k X0 (k X1 (τ X2)))
       have i₂ := eq109 X1 X2 X0
       grind)
    | exact superpose eq109 eq31
    | exact resolve eq31 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq75991 : ∀ X0 X1 X2 X3 : G, (σ (k (k (k (τ X0) X1) X2) X3)) = (k (k (k X0 (σ X1)) (σ X2)) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 (k (k (τ X0) X1) X2) X3
       have i₂ := eq129 X0 X1 X2
       grind)
    | exact superpose eq129 eq15
    | exact resolve eq15 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq114230 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq9151 eq130
    | exact resolve eq130 eq9151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9151
  have eq114238 : ∀ X0 X1 X2 : G, (k (σ (σ X0)) (k X1 (σ X2))) = (σ (σ (k X0 (τ (k (τ X1) X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130 X1 X2 (σ X0)
       have i₂ := eq55 (k (τ X1) X2) X0
       grind)
    | exact superpose eq55 eq130
    | exact resolve eq130 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq114384 : ∀ X0 X1 X2 : G, (k (σ (σ X0)) (k X1 (σ X2))) = (σ (σ (k X0 (k (τ (τ X1)) (τ X2))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114238 X0 X1 X2
       have i₂ := eq148 (τ X1) X2
       grind)
    | exact superpose eq148 eq114238
    | exact resolve eq114238 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114238
  have eq114389 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (k (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq114230
    | (have j0 := eq114230 X0
       grind)
    | exact resolve eq114230 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114230
  have eq115162 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (k (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq21 eq114389
    | (have j0 := eq114389 (M.op x y)
       grind)
    | exact resolve eq114389 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114389
  have eq115194 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) := by grind
  clear eq115162
  have eq115211 : (σ (M.op x y)) = (k (σ (M.op x y)) (k (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq21 eq115194
    | exact resolve eq115194 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115194
  have eq116378 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op x y) X0))) = (σ (M.op (M.op x y) (M.op X0 (M.op (τ X1) (M.op x y))))) ∨ (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 (M.op (τ X1) (M.op x y)))) ∨ (τ X1) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq1348 eq283
    | (have j0 := eq283 (M.op (M.op x y) X0) X1
       grind)
    | exact resolve eq283 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq1348
  have eq330094 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op (M.op x y) X0))) = (σ (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op x y))))) ∨ (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq42 eq116378
    | exact resolve eq116378 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330097 : ∀ X0 : G, (σ (M.op (M.op x y) (τ X0))) = (k X0 (σ (M.op (M.op x y) (M.op x y)))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1258 eq116378
    | (have j0 := eq116378 (M.op x y) X0
       grind)
    | exact resolve eq116378 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116378
  have eq330105 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (M.op x y) (τ X0))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq330097 X0
       have i₂ := eq1199 sF0
       grind)
    | exact superpose eq1199 eq330097
    | (have j0 := eq330097 X0
       grind)
    | exact resolve eq330097 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330097
  have eq330108 : ∀ X0 : G, (σ X0) = (k (σ (M.op x y)) (σ (M.op (M.op x y) X0))) ∨ (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1196 eq330094
    | (have j0 := eq330094 X0
       grind)
    | exact resolve eq330094 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330094
  have eq330116 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (M.op x y) (τ X0))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq330105
    | (have j0 := eq330105 X0
       grind)
    | exact resolve eq330105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330105
  have eq330118 : ∀ X0 : G, (σ X0) = (σ (k (M.op x y) (M.op (M.op x y) X0))) ∨ (M.op (M.op x y) X0) = (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq29 eq330108
    | (have j0 := eq330108 X0
       grind)
    | exact resolve eq330108 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330108
  have eq330124 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (k X0 (σ (M.op x y))) = (σ (M.op (M.op x y) (τ X0))) ∨ (τ X0) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq330116 X0
       have i₂ := eq1199 sF0
       grind)
    | exact superpose eq1199 eq330116
    | (have j0 := eq330116 X0
       grind)
    | exact resolve eq330116 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330116
  have eq330126 : ∀ X0 : G, (σ X0) = (σ (k (M.op x y) (M.op (M.op x y) X0))) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1196 eq330118
    | (have j0 := eq330118 X0
       grind)
    | exact resolve eq330118 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330118
  have eq330131 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (σ (M.op (M.op x y) (τ X0))) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq330124 X0
       have i₂ := eq1199 sF0
       grind)
    | exact superpose eq1199 eq330124
    | (have j0 := eq330124 X0
       grind)
    | exact resolve eq330124 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330124
  have eq330144 : ∀ X0 : G, (τ (σ X0)) = (k (M.op x y) (M.op (M.op x y) X0)) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq330126 eq10
    | (have j1 := eq330126 X0
       grind)
    | exact resolve eq10 eq330126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330126
  have eq330172 : ∀ X0 : G, (k (M.op x y) (M.op (M.op x y) X0)) = X0 ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq330144 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq330144
    | (have j0 := eq330144 X0
       grind)
    | exact resolve eq330144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330144
  have eq330185 : ∀ X0 : G, (τ X0) = (k (τ (M.op x y)) (τ (M.op (M.op x y) X0))) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq330172 eq148
    | (have j1 := eq330172 X0
       grind)
    | exact resolve eq148 eq330172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330172
  have eq330204 : ∀ X0 X1 : G, (k (k X0 (σ (M.op x y))) (σ X1)) = (σ (k (M.op (M.op x y) (τ X0)) X1)) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq330131 eq15
    | (have j1 := eq330131 X0
       grind)
    | exact resolve eq15 eq330131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330205 : ∀ X0 X1 : G, (σ (k X1 (M.op (M.op x y) (τ X0)))) = (k (σ X1) (k X0 (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq330131 eq15
    | (have j1 := eq330131 X0
       grind)
    | exact resolve eq15 eq330131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330131
  have eq330246 : ∀ X0 : G, (τ (τ X0)) = (k (τ (τ (M.op x y))) (τ (τ (M.op (M.op x y) X0)))) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq330185 eq148
    | (have j1 := eq330185 X0
       grind)
    | exact resolve eq148 eq330185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330185
  have eq331893 : ∀ X0 X1 : G, (σ (k (τ (τ X0)) (τ X1))) = (k (k (σ (τ (τ (M.op x y)))) (τ (M.op (M.op x y) X0))) X1) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq330246 eq102
    | (have j1 := eq330246 X0
       grind)
    | exact resolve eq102 eq330246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq330246
  have eq331907 : ∀ X0 X1 : G, (σ (k (τ (τ X0)) (τ X1))) = (k (k (τ (M.op x y)) (τ (M.op (M.op x y) X0))) X1) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq331893 X0 X1
       have i₂ := eq11 (τ sF0)
       grind)
    | exact superpose eq11 eq331893
    | (have j0 := eq331893 X0 X1
       grind)
    | exact resolve eq331893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331893
  have eq331919 : ∀ X0 X1 : G, (k (τ X0) (σ (τ X1))) = (k (k (τ (M.op x y)) (τ (M.op (M.op x y) X0))) X1) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq331907 X0 X1
       have i₂ := eq56 (τ X0) (τ X1)
       grind)
    | exact superpose eq56 eq331907
    | (have j0 := eq331907 X0 X1
       grind)
    | exact resolve eq331907 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331907
  have eq331929 : ∀ X0 X1 : G, (k (τ X0) X1) = (k (k (τ (M.op x y)) (τ (M.op (M.op x y) X0))) X1) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq331919 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq331919
    | (have j0 := eq331919 X0 X1
       grind)
    | exact resolve eq331919 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331919
  have eq388282 : ∀ X0 X1 : G, (k (σ (M.op (M.op x y) (τ X0))) X1) = (k (k X0 (σ (M.op x y))) (σ (τ X1))) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq330204 eq55
    | (have j1 := eq330204 X0 X1
       grind)
    | exact resolve eq55 eq330204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330204
  have eq388325 : ∀ X0 X1 : G, (k (k X0 (σ (M.op x y))) X1) = (k (σ (M.op (M.op x y) (τ X0))) X1) ∨ (M.op x y) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq388282 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq388282
    | (have j0 := eq388282 X0 X1
       grind)
    | exact resolve eq388282 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388282
  have eq388347 : ∀ X0 X1 : G, (k (k (σ X0) (σ (M.op x y))) X1) = (k (σ (M.op (M.op x y) X0)) X1) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388325 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq388325
    | exact resolve eq388325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388325
  have eq388422 : ∀ X0 X1 : G, (k (σ (k X0 (M.op x y))) X1) = (k (σ (M.op (M.op x y) X0)) X1) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq31 eq388347
    | (have j0 := eq388347 X0 X1
       grind)
    | exact resolve eq388347 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388347
  have eq388627 : ∀ X0 X1 : G, (k (τ (σ (k X0 (M.op x y)))) (τ X1)) = (τ (k (σ (M.op (M.op x y) X0)) X1)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq388422 eq148
    | (have j1 := eq388422 X0 X1
       grind)
    | exact resolve eq148 eq388422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388422
  have eq388669 : ∀ X0 X1 : G, (k (τ (σ (k X0 (M.op x y)))) (τ X1)) = (k (τ (σ (M.op (M.op x y) X0))) (τ X1)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388627 X0 X1
       have i₂ := eq148 (σ (M.op sF0 X0)) X1
       grind)
    | exact superpose eq148 eq388627
    | (have j0 := eq388627 X0 X1
       grind)
    | exact resolve eq388627 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388627
  have eq388684 : ∀ X0 X1 : G, (k (M.op (M.op x y) X0) (τ X1)) = (k (τ (σ (k X0 (M.op x y)))) (τ X1)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388669 X0 X1
       have i₂ := eq10 (M.op sF0 X0)
       grind)
    | exact superpose eq10 eq388669
    | (have j0 := eq388669 X0 X1
       grind)
    | exact resolve eq388669 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388669
  have eq388688 : ∀ X0 X1 : G, (k (k X0 (M.op x y)) (τ X1)) = (k (M.op (M.op x y) X0) (τ X1)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388684 X0 X1
       have i₂ := eq10 (k X0 sF0)
       grind)
    | exact superpose eq10 eq388684
    | (have j0 := eq388684 X0 X1
       grind)
    | exact resolve eq388684 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388684
  have eq390256 : ∀ X0 X1 : G, (k (σ (k X0 (M.op x y))) X1) = (σ (k (M.op (M.op x y) X0) (τ X1))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq388688 eq55
    | (have j1 := eq388688 X0 X1
       grind)
    | exact resolve eq55 eq388688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388688
  have eq390476 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (k (σ (k (M.op X0 (M.op x y)) (M.op x y))) X1) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1258 eq390256
    | (have j0 := eq390256 X0 X1
       grind)
    | exact resolve eq390256 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390256
  have eq390842 : ∀ X0 X1 : G, (σ (k X0 (τ (σ X1)))) = (σ (k (k (M.op X0 (M.op x y)) (M.op x y)) X1)) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq390476 eq15
    | (have j1 := eq390476 X0 X1
       grind)
    | exact resolve eq15 eq390476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390476
  have eq390919 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k (k (M.op X0 (M.op x y)) (M.op x y)) X1)) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq390842 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq390842
    | (have j0 := eq390842 X0 X1
       grind)
    | exact resolve eq390842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390842
  have eq392662 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (k (k (M.op X0 (M.op x y)) (M.op x y)) X1) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq390919 eq10
    | (have j1 := eq390919 X0 X1
       grind)
    | exact resolve eq10 eq390919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390919
  have eq392700 : ∀ X0 X1 : G, (k X0 X1) = (k (k (M.op X0 (M.op x y)) (M.op x y)) X1) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq392662 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq392662
    | (have j0 := eq392662 X0 X1
       grind)
    | exact resolve eq392662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392662
  have eq405585 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op x y) (τ X1)))) = (k (σ (τ X0)) (k X1 (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (τ X1)) ∨ (M.op x y) = (τ X1) := by
    intro X0 X1
    first
    | exact superpose eq330205 eq56
    | (have j1 := eq330205 X1 X1
       grind)
    | exact resolve eq56 eq330205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330205
  have eq405647 : ∀ X0 X1 : G, (k X0 (k X1 (σ (M.op x y)))) = (k X0 (σ (M.op (M.op x y) (τ X1)))) ∨ (M.op x y) = (M.op (M.op x y) (τ X1)) ∨ (M.op x y) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq405585 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq405585
    | (have j0 := eq405585 X0 X1
       grind)
    | exact resolve eq405585 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405585
  have eq405727 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op x y) X0))) = (k X1 (k (σ X0) (σ (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq405647 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq405647
    | exact resolve eq405647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405647
  have eq405795 : ∀ X0 X1 : G, (k X1 (σ (k X0 (M.op x y)))) = (k X1 (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq31 eq405727
    | (have j0 := eq405727 X0 X1
       grind)
    | exact resolve eq405727 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405727
  have eq405979 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ (k X0 (M.op x y))) (σ (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    grind
  clear eq405795
  have eq406049 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (σ (k (k X0 (M.op x y)) (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq405979 X0
       have i₂ := eq15 (k X0 sF0) (M.op sF0 X0)
       grind)
    | exact superpose eq15 eq405979
    | (have j0 := eq405979 X0
       grind)
    | exact resolve eq405979 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405979
  have eq407554 : ∀ X0 : G, (τ (σ (k X0 (M.op x y)))) = (k (k X0 (M.op x y)) (M.op (M.op x y) X0)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq406049 eq10
    | (have j1 := eq406049 X0
       grind)
    | exact resolve eq10 eq406049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406049
  have eq407597 : ∀ X0 : G, (k X0 (M.op x y)) = (k (k X0 (M.op x y)) (M.op (M.op x y) X0)) ∨ (M.op x y) = (M.op (M.op x y) X0) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq407554 X0
       have i₂ := eq10 (k X0 sF0)
       grind)
    | exact superpose eq10 eq407554
    | (have j0 := eq407554 X0
       grind)
    | exact resolve eq407554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407554
  have eq407612 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op x y)) = (k (k (M.op X0 (M.op x y)) (M.op x y)) X0) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1258 eq407597
    | (have j0 := eq407597 X0
       grind)
    | exact resolve eq407597 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407597
  have eq425216 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq407612 eq392700
    | (have j0 := eq392700 X0 x
       have j1 := eq407612 X0
       grind)
    | exact resolve eq392700 eq407612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392700 eq407612
  have eq425276 : ∀ X0 : G, (k X0 X0) = (k (M.op X0 (M.op x y)) (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq425216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425216
  have eq425293 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    grind
  clear eq425276
  have eq425360 : ∀ X0 : G, (τ X0) = (k (τ (M.op X0 (M.op x y))) (τ (M.op x y))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq425293 eq148
    | (have j1 := eq425293 X0
       grind)
    | exact resolve eq148 eq425293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642098 : ∀ X0 X1 : G, (k (τ (M.op X0 (M.op x y))) X1) = (k (k (τ (M.op x y)) (τ X0)) X1) ∨ (M.op X0 (M.op x y)) = X0 ∨ (M.op x y) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1258 eq331929
    | exact resolve eq331929 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331929
  have eq642174 : ∀ X0 : G, (τ X0) = (k (k (τ (M.op x y)) (τ X0)) (τ (M.op x y))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq642098 eq425360
    | (have j0 := eq425360 X0
       have j1 := eq642098 X0 x
       grind)
    | exact resolve eq425360 eq642098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425360 eq642098
  have eq642201 : ∀ X0 : G, (τ X0) = (k (k (τ (M.op x y)) (τ X0)) (τ (M.op x y))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq642174 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642174
  have eq797996 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ (M.op x y))) X0) (σ (τ (M.op x y)))) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq642201 eq108
    | (have j1 := eq642201 X0
       grind)
    | exact resolve eq108 eq642201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642201
  have eq797999 : ∀ X0 : G, (σ (τ X0)) = (k (k (M.op x y) X0) (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq797996 X0
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq797996
    | (have j0 := eq797996 X0
       grind)
    | exact resolve eq797996 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797996
  have eq798002 : ∀ X0 : G, (k (k (M.op x y) X0) (M.op x y)) = X0 ∨ (M.op x y) = X0 ∨ (M.op x y) = (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq797999 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq797999
    | (have j0 := eq797999 X0
       grind)
    | exact resolve eq797999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797999
  have eq798010 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) ∨ (τ X0) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq798002 eq112
    | (have j1 := eq798002 (τ X0)
       grind)
    | exact resolve eq112 eq798002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq798002
  have eq798026 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) ∨ (τ X0) = (M.op (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq798010
    | (have j0 := eq798010 X0
       grind)
    | exact resolve eq798010 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798010
  have eq798027 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op x y)) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (M.op (τ X0) (M.op x y)) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq798026 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq798026
    | (have j0 := eq798026 X0
       grind)
    | exact resolve eq798026 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798026
  have eq837567 : ∀ X0 : G, (M.op x y) = (M.op (τ X0) (M.op x y)) ∨ (τ X0) = (M.op x y) ∨ (τ X0) = (M.op (M.op x y) (τ X0)) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq798027 eq1258
    | (have j1 := eq798027 X0
       grind)
    | exact resolve eq1258 eq798027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798027
  have eq862140 : ∀ X0 : G, (τ X0) = (M.op (M.op x y) (M.op x y)) ∨ (τ X0) = (M.op x y) ∨ (τ X0) = (M.op (M.op x y) (τ X0)) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq837567 eq1258
    | (have j1 := eq837567 X0
       grind)
    | exact resolve eq1258 eq837567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837567
  have eq862145 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (τ X0) = (M.op x y) ∨ (τ X0) = (M.op (M.op x y) (τ X0)) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq862140 X0
       have i₂ := eq1199 sF0
       grind)
    | exact superpose eq1199 eq862140
    | (have j0 := eq862140 X0
       grind)
    | exact resolve eq862140 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862140
  have eq862146 : ∀ X0 : G, (τ X0) = (M.op (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq862145 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862145
  have eq862168 : ∀ X0 : G, (M.op (τ X0) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (τ X0) (M.op x y))) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq862146 eq1836
    | (have j1 := eq862146 X0
       grind)
    | exact resolve eq1836 eq862146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862146
  have eq862176 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op x y)) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq1195 eq862168
    | (have j0 := eq862168 X0
       grind)
    | exact resolve eq862168 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862168
  have eq862618 : ∀ X0 : G, (τ X0) = (k (τ X0) (M.op x y)) ∨ (τ X0) = (M.op x y) ∨ (τ X0) = (M.op x y) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq862176 eq425293
    | (have j0 := eq425293 (τ X0)
       have j1 := eq862176 X0
       grind)
    | exact resolve eq425293 eq862176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425293
  have eq862619 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op x y) ∨ (τ X0) = (k (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq862176 eq13
    | (have j0 := eq13 (τ X0) (M.op x y)
       have j1 := eq862176 X0
       grind)
    | (have r₁ := eq13 (M.op x y) (τ X0)
       have r₂ := eq862176 X0
       grind)
    | exact resolve eq13 eq862176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862176
  have eq862628 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op x y) ∨ (τ X0) = (k (M.op x y) (τ X0)) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq862619 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862619
  have eq862629 : ∀ X0 : G, (τ X0) = (k (M.op x y) (τ X0)) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq862628 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862628
  have eq862630 : ∀ X0 : G, (τ X0) = (k (τ X0) (M.op x y)) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq862618 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862618
  have eq875941 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (k (k (σ (M.op x y)) X0) X1) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq862629 eq52978
    | (have j1 := eq862629 X0
       grind)
    | exact resolve eq52978 eq862629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52978
  have eq875959 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (k (k (σ (M.op x y)) X0) X1) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq21 eq875941
    | (have j0 := eq875941 X0 X1
       grind)
    | exact resolve eq875941 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875941
  have eq875996 : ∀ X0 X1 : G, (k X0 X1) = (k (k (σ (M.op x y)) X0) X1) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq875959 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq875959
    | (have j0 := eq875959 X0 X1
       grind)
    | exact resolve eq875959 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875959
  have eq903066 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq862630 eq56
    | (have j1 := eq862630 X0
       grind)
    | exact resolve eq56 eq862630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq862630
  have eq903072 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op x y))) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq903066
    | (have j0 := eq903066 X0
       grind)
    | exact resolve eq903066 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903066
  have eq903080 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq903072 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq903072
    | (have j0 := eq903072 X0
       grind)
    | exact resolve eq903072 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903072
  have eq903086 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k X0 (σ (M.op x y))) = X0 ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0
       have i₂ := eq903080 X0
       grind)
    | exact superpose eq903080 eq11
    | (have j1 := eq903080 X0
       grind)
    | exact resolve eq11 eq903080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903080
  have eq903149 : ∀ X0 : G, (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (k X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq903086
    | (have j0 := eq903086 X0
       grind)
    | exact resolve eq903086 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903086
  have eq1296849 : ∀ X0 X1 : G, (σ (M.op x y)) = X0 ∨ (k X0 X1) = (k (k (σ (M.op x y)) X0) X1) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0
       have i₂ := eq875996 X0 X1
       grind)
    | exact superpose eq875996 eq11
    | (have j1 := eq875996 X0 X1
       grind)
    | exact resolve eq11 eq875996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875996
  have eq1296854 : ∀ X0 X1 : G, (k X0 X1) = (k (k (σ (M.op x y)) X0) X1) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq21 eq1296849
    | (have j0 := eq1296849 X0 X1
       grind)
    | exact resolve eq1296849 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296849
  have eq1301631 : ∀ X0 : G, (k X0 (σ (M.op x y))) ≠ X0 ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1296854 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1296854
  have eq1301635 : ∀ X0 : G, (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1301631 X0
       have j1 := eq903149 X0
       grind)
    | (have r₁ := eq1301631 X0
       have r₂ := eq903149 X0
       grind)
    | (have r₁ := eq1301631 (σ (M.op x y))
       have r₂ := eq903149 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq1301631 eq903149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903149 eq1301631
  have eq1302298 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (σ (M.op x y))) X0) (σ (σ (M.op x y)))) ∨ (τ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1301635 eq108
    | (have j1 := eq1301635 (τ X0)
       grind)
    | exact resolve eq108 eq1301635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1302322 : ∀ X0 : G, (τ X0) = (k (τ (k (σ (M.op x y)) X0)) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq1301635 eq148
    | (have j1 := eq1301635 X0
       grind)
    | exact resolve eq148 eq1301635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301635
  have eq1302369 : ∀ X0 : G, (τ X0) = (k (τ (k (σ (M.op x y)) X0)) (M.op x y)) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq42 eq1302322
    | (have j0 := eq1302322 X0
       grind)
    | exact resolve eq1302322 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302322
  have eq1302386 : ∀ X0 : G, (τ X0) = (σ (M.op x y)) ∨ (k (k (σ (σ (M.op x y))) X0) (σ (σ (M.op x y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1302298 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1302298
    | (have j0 := eq1302298 X0
       grind)
    | exact resolve eq1302298 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302298
  have eq1302716 : ∀ X0 : G, (τ X0) = (k (k (τ (σ (M.op x y))) (τ X0)) (M.op x y)) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1302369 x
       have i₂ := eq148 sF1 x
       grind)
    | exact superpose eq148 eq1302369
    | (have j0 := eq1302369 X0
       grind)
    | exact resolve eq1302369 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302369
  have eq1302944 : ∀ X0 : G, (τ X0) = (k (k (M.op x y) (τ X0)) (M.op x y)) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq42 eq1302716
    | (have j0 := eq1302716 X0
       grind)
    | exact resolve eq1302716 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302716
  have eq1303452 : ∀ X0 : G, (k (k (M.op x y) X0) (M.op x y)) = X0 ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1302944 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1302944
    | (have j0 := eq1302944 (σ X0)
       grind)
    | exact resolve eq1302944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302944
  have eq1304158 : ∀ X0 : G, (τ X0) = (k (τ (k (M.op x y) X0)) (τ (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1303452 eq148
    | (have j1 := eq1303452 X0
       grind)
    | exact resolve eq148 eq1303452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303452
  have eq1304176 : ∀ X0 : G, (τ X0) = (k (k (τ (M.op x y)) (τ X0)) (τ (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1304158 x
       have i₂ := eq148 sF0 x
       grind)
    | exact superpose eq148 eq1304158
    | (have j0 := eq1304158 X0
       grind)
    | exact resolve eq1304158 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304158
  have eq1304357 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (k X0 (σ (M.op x y)))) ∨ (k (k (σ (σ (M.op x y))) X1) (σ (σ (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 X0
       have i₂ := eq1302386 X1
       grind)
    | exact superpose eq1302386 eq55
    | (have j1 := eq1302386 X1
       grind)
    | exact resolve eq55 eq1302386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1304485 : (M.op x y) = (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (k (σ (σ (M.op x y))) (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | (have i₁ := eq42
       have i₂ := eq1302386 sF1
       grind)
    | exact superpose eq1302386 eq42
    | (have j1 := eq1302386 (σ (M.op x y))
       grind)
    | exact resolve eq42 eq1302386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302386
  have eq1304488 : (σ (M.op x y)) = (k (k (σ (σ (M.op x y))) (σ (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | (have r₁ := eq1304485
       have r₂ := eq1316
       grind)
    | exact resolve eq1304485 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304485
  have eq1304519 : (σ (M.op x y)) = (k (σ (k (σ (M.op x y)) (M.op x y))) (σ (σ (M.op x y)))) := by
    first
    | exact superpose eq31 eq1304488
    | exact resolve eq1304488 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304488
  have eq1304524 : (σ (M.op x y)) = (σ (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq1304519
       have i₂ := eq15 (k sF1 sF0) sF1
       grind)
    | exact superpose eq15 eq1304519
    | exact resolve eq1304519 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304519
  have eq1304791 : (τ (σ (M.op x y))) = (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1304524 eq10
    | exact resolve eq10 eq1304524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1304856 : ∀ X0 X1 : G, (k (k (σ X0) (k (σ (M.op x y)) X1)) (σ (M.op x y))) = (σ (k (k X0 (k (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))) (τ X1))) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1304524 eq75883
    | exact resolve eq75883 eq1304524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75883
  have eq1304880 : ∀ X0 X1 : G, (k (σ (σ X0)) (k X1 (σ (M.op x y)))) = (σ (σ (k X0 (k (τ (τ X1)) (τ (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y)))))))) := by
    intro X0 X1
    first
    | exact superpose eq1304524 eq114384
    | exact resolve eq114384 eq1304524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114384 eq1304524
  have eq1305021 : ∀ X0 X1 : G, (k (σ (σ X0)) (k X1 (σ (M.op x y)))) = (σ (σ (k X0 (k (τ (τ X1)) (k (τ (k (σ (M.op x y)) (M.op x y))) (τ (σ (M.op x y)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1304880 X0 X1
       have i₂ := eq148 (k sF1 sF0) sF1
       grind)
    | exact superpose eq148 eq1304880
    | exact resolve eq1304880 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304880
  have eq1305041 : (M.op x y) = (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42 eq1304791
    | exact resolve eq1304791 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304791
  have eq1305045 : ∀ X0 X1 : G, (k (σ (σ X0)) (k X1 (σ (M.op x y)))) = (σ (σ (k X0 (k (τ (τ X1)) (k (τ (k (σ (M.op x y)) (M.op x y))) (M.op x y)))))) := by
    intro X0 X1
    first
    | exact superpose eq42 eq1305021
    | exact resolve eq1305021 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305021
  have eq1306510 : ∀ X0 X1 : G, (σ (k (k X0 (k (M.op x y) (τ X1))) (M.op x y))) = (k (k (σ X0) (k (σ (M.op x y)) X1)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1305041 eq1304856
    | exact resolve eq1304856 eq1305041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304856
  have eq1306534 : ∀ X0 X1 : G, (k (σ (σ X0)) (k X1 (σ (M.op x y)))) = (σ (σ (k X0 (k (τ (τ X1)) (k (k (τ (σ (M.op x y))) (τ (M.op x y))) (M.op x y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1305045 X0 X1
       have i₂ := eq148 sF1 sF0
       grind)
    | exact superpose eq148 eq1305045
    | exact resolve eq1305045 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305045
  have eq1307232 : ∀ X0 X1 : G, (k (σ (σ X0)) (k X1 (σ (M.op x y)))) = (σ (σ (k X0 (k (τ (τ X1)) (k (k (M.op x y) (τ (M.op x y))) (M.op x y)))))) := by
    intro X0 X1
    first
    | exact superpose eq42 eq1306534
    | exact resolve eq1306534 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306534
  have eq1308022 : (τ (M.op x y)) = (k (τ (k (σ (M.op x y)) (M.op x y))) (τ (σ (M.op x y)))) := by
    first
    | exact superpose eq1305041 eq148
    | exact resolve eq148 eq1305041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1308031 : (τ (M.op x y)) = (k (τ (k (σ (M.op x y)) (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq42 eq1308022
    | exact resolve eq1308022 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308022
  have eq1308058 : (τ (M.op x y)) = (k (k (τ (σ (M.op x y))) (τ (M.op x y))) (M.op x y)) := by
    first
    | (have i₁ := eq1308031
       have i₂ := eq148 sF1 sF0
       grind)
    | exact superpose eq148 eq1308031
    | exact resolve eq1308031 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308031
  have eq1308067 : (τ (M.op x y)) = (k (k (M.op x y) (τ (M.op x y))) (M.op x y)) := by
    first
    | exact superpose eq42 eq1308058
    | exact resolve eq1308058 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308058
  have eq1308465 : ∀ X0 X1 : G, (σ (σ (k X0 (k (τ (τ X1)) (τ (M.op x y)))))) = (k (σ (σ X0)) (k X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1308067 eq1307232
    | exact resolve eq1307232 eq1308067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307232 eq1308067
  have eq1322742 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (k (τ (M.op x y)) (τ X0))) (M.op x y)) (σ (τ X0))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1304176 eq53062
    | (have j1 := eq1304176 X0
       grind)
    | exact resolve eq53062 eq1304176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304176
  have eq1322749 : ∀ X0 : G, (σ (τ X0)) = (σ (k (k (k (τ (M.op x y)) (τ X0)) (τ (M.op x y))) (τ X0))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1322742 X0
       have i₂ := eq108 (k (τ sF0) (τ X0)) sF0 (τ X0)
       grind)
    | exact superpose eq108 eq1322742
    | (have j0 := eq1322742 X0
       grind)
    | exact resolve eq1322742 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322742
  have eq1322797 : ∀ X0 : G, (σ (τ X0)) = (k (k (k (M.op x y) (σ (τ X0))) (σ (τ (M.op x y)))) (σ (τ X0))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1322749 X0
       have i₂ := eq75991 sF0 (τ X0) (τ sF0) (τ X0)
       grind)
    | exact superpose eq75991 eq1322749
    | (have j0 := eq1322749 X0
       grind)
    | exact resolve eq1322749 eq75991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75991 eq1322749
  have eq1322831 : ∀ X0 : G, (k (k (k (M.op x y) X0) (σ (τ (M.op x y)))) X0) = X0 ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1322797 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1322797
    | (have j0 := eq1322797 X0
       grind)
    | exact resolve eq1322797 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322797
  have eq1322858 : ∀ X0 : G, (k (k (k (M.op x y) X0) (M.op x y)) X0) = X0 ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1322831 X0
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq1322831
    | (have j0 := eq1322831 X0
       grind)
    | exact resolve eq1322831 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322831
  have eq1323393 : ∀ X0 : G, (σ (τ X0)) = (k (k (k (σ (M.op x y)) X0) (σ (M.op x y))) X0) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1322858 eq53114
    | (have j1 := eq1322858 (τ X0)
       grind)
    | exact resolve eq53114 eq1322858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53114
  have eq1323438 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (k (k (M.op x y) (τ X0)) (M.op x y))) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1322858 eq53062
    | (have j1 := eq1322858 (τ X0)
       grind)
    | exact resolve eq53062 eq1322858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53062 eq1322858
  have eq1323452 : ∀ X0 : G, (σ (τ X0)) = (σ (k (k (k (k (M.op x y) (τ X0)) (M.op x y)) (τ X0)) (τ X0))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1323438 x
       have i₂ := eq108 (k (k sF0 (τ x)) sF0) x (τ x)
       grind)
    | exact superpose eq108 eq1323438
    | (have j0 := eq1323438 X0
       grind)
    | exact resolve eq1323438 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323438
  have eq1323467 : ∀ X0 : G, (σ (τ X0)) = (k (k (k (σ (M.op x y)) X0) (σ (M.op x y))) X0) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq1323393
    | (have j0 := eq1323393 X0
       grind)
    | exact resolve eq1323393 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323393
  have eq1323483 : ∀ X0 : G, (σ (τ X0)) = (k (k (k (k (σ (M.op x y)) X0) (σ (M.op x y))) X0) X0) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq52964 eq1323452
    | (have j0 := eq1323452 X0
       grind)
    | exact resolve eq1323452 eq52964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52964 eq1323452
  have eq1323495 : ∀ X0 : G, (k (k (k (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1323467 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1323467
    | (have j0 := eq1323467 X0
       grind)
    | exact resolve eq1323467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323467
  have eq1323509 : ∀ X0 : G, (σ (τ X0)) = (k (k (k (k (σ (M.op x y)) X0) (σ (M.op x y))) X0) X0) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq1323483
    | (have j0 := eq1323483 X0
       grind)
    | exact resolve eq1323483 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323483
  have eq1323519 : ∀ X0 : G, (k (k (k (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1323495 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1323495
    | (have j0 := eq1323495 X0
       grind)
    | exact resolve eq1323495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323495
  have eq1323532 : ∀ X0 : G, (k (k (k (k (σ (M.op x y)) X0) (σ (M.op x y))) X0) X0) = X0 ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1323509 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1323509
    | (have j0 := eq1323509 X0
       grind)
    | exact resolve eq1323509 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323509
  have eq1323547 : ∀ X0 : G, (k (k (k (k (σ (M.op x y)) X0) (σ (M.op x y))) X0) X0) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1323532 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1323532
    | (have j0 := eq1323532 X0
       grind)
    | exact resolve eq1323532 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323532
  have eq1447941 : ∀ X0 X1 : G, (k (τ (σ X0)) (τ X1)) = (τ (σ (k X0 (σ (M.op x y))))) ∨ (k (k (σ (σ (M.op x y))) X1) (σ (σ (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 (σ X0) X1
       have i₂ := eq1304357 X0 X1
       grind)
    | exact superpose eq1304357 eq148
    | (have j1 := eq1304357 X0 X1
       grind)
    | exact resolve eq148 eq1304357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304357
  have eq1447978 : ∀ X0 X1 : G, (k X0 (σ (M.op x y))) = (k (τ (σ X0)) (τ X1)) ∨ (k (k (σ (σ (M.op x y))) X1) (σ (σ (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1447941 X0 X1
       have i₂ := eq10 (k X0 sF1)
       grind)
    | exact superpose eq10 eq1447941
    | (have j0 := eq1447941 X0 X1
       grind)
    | exact resolve eq1447941 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447941
  have eq1447997 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k X0 (σ (M.op x y))) ∨ (k (k (σ (σ (M.op x y))) X1) (σ (σ (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1447978 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1447978
    | (have j0 := eq1447978 X0 X1
       grind)
    | exact resolve eq1447978 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447978
  have eq1455022 : ∀ X0 X1 : G, (k X1 X0) = (k X1 (σ (M.op x y))) ∨ (σ X0) = (k (k (σ (σ (M.op x y))) (σ X0)) (σ (σ (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1447997 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1447997
    | (have j0 := eq1447997 X0 (σ X0)
       grind)
    | exact resolve eq1447997 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447997
  have eq1455127 : ∀ X0 X1 : G, (σ X0) = (k (σ (k (σ (M.op x y)) X0)) (σ (σ (M.op x y)))) ∨ (k X1 X0) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1455022 X1 X1
       have i₂ := eq15 sF1 X1
       grind)
    | exact superpose eq15 eq1455022
    | (have j0 := eq1455022 X0 X1
       grind)
    | exact resolve eq1455022 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455022
  have eq1455133 : ∀ X0 X1 : G, (σ X0) = (σ (k (k (σ (M.op x y)) X0) (σ (M.op x y)))) ∨ (k X1 X0) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1455127 X0 X1
       have i₂ := eq15 (k sF1 X0) sF1
       grind)
    | exact superpose eq15 eq1455127
    | (have j0 := eq1455127 X0 X1
       grind)
    | exact resolve eq1455127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455127
  have eq1465692 : ∀ X0 X1 : G, (τ (σ X0)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (k X1 X0) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq1455133 eq10
    | (have j1 := eq1455133 X0 X1
       grind)
    | exact resolve eq10 eq1455133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1455133
  have eq1465859 : ∀ X0 X1 : G, (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (k X1 X0) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1465692 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1465692
    | (have j0 := eq1465692 X0 X1
       grind)
    | exact resolve eq1465692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465692
  have eq1466276 : ∀ X0 X1 : G, (τ X0) = (k (τ (k (σ (M.op x y)) X0)) (τ (σ (M.op x y)))) ∨ (k X1 X0) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq148 X1 X0
       have i₂ := eq1465859 X0 X1
       grind)
    | exact superpose eq1465859 eq148
    | (have j1 := eq1465859 X0 X1
       grind)
    | exact resolve eq148 eq1465859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465859
  have eq1466752 : ∀ X0 X1 : G, (τ X0) = (k (τ (k (σ (M.op x y)) X0)) (M.op x y)) ∨ (k X1 X0) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq42 eq1466276
    | (have j0 := eq1466276 X0 X1
       grind)
    | exact resolve eq1466276 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466276
  have eq1466886 : ∀ X0 X1 : G, (τ X0) = (k (k (τ (σ (M.op x y))) (τ X0)) (M.op x y)) ∨ (k X1 X0) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1466752 X1 X1
       have i₂ := eq148 sF1 X1
       grind)
    | exact superpose eq148 eq1466752
    | (have j0 := eq1466752 X0 X1
       grind)
    | exact resolve eq1466752 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466752
  have eq1466930 : ∀ X0 X1 : G, (τ X0) = (k (k (M.op x y) (τ X0)) (M.op x y)) ∨ (k X1 X0) = (k X1 (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq42 eq1466886
    | (have j0 := eq1466886 X0 X1
       grind)
    | exact resolve eq1466886 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1466886
  have eq1487071 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ (M.op x y))) ∨ (τ (σ X1)) = (k (k (M.op x y) (τ (σ X1))) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1466930 (σ X1) (σ X0)
       grind)
    | (have i₁ := eq15 X0 (M.op x y)
       have i₂ := eq1466930 X0 (σ X0)
       grind)
    | exact superpose eq1466930 eq15
    | (have j1 := eq1466930 (σ X1) X1
       grind)
    | exact resolve eq15 eq1466930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466930
  have eq1487095 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (k X0 (M.op x y))) ∨ (τ (σ X1)) = (k (k (M.op x y) (τ (σ X1))) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq31 eq1487071
    | (have j0 := eq1487071 X0 X1
       grind)
    | exact resolve eq1487071 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487071
  have eq1487123 : ∀ X0 X1 : G, (k (k (M.op x y) X1) (M.op x y)) = X1 ∨ (σ (k X0 X1)) = (σ (k X0 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1487095 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1487095
    | (have j0 := eq1487095 X0 X1
       grind)
    | exact resolve eq1487095 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487095
  have eq1491279 : ∀ X0 X1 : G, (k X0 (M.op x y)) = (τ (σ (k X0 X1))) ∨ (k (k (M.op x y) X1) (M.op x y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 X0
       have i₂ := eq1487123 X0 (σ X0)
       grind)
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq1487123 X0 X1
       grind)
    | exact superpose eq1487123 eq10
    | (have j1 := eq1487123 X0 X1
       grind)
    | exact resolve eq10 eq1487123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487123
  have eq1491293 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (M.op x y)) ∨ (k (k (M.op x y) X1) (M.op x y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1491279 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1491279
    | (have j0 := eq1491279 X0 X1
       grind)
    | exact resolve eq1491279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491279
  have eq1492888 : ∀ X0 : G, (M.op x y) = (k (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))) X0) ∨ (M.op x y) = (σ (M.op x y)) ∨ (k (k (M.op x y) X0) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1323519 x
       have i₂ := eq1491293 (k (k sF1 x) sF1) x
       grind)
    | (have i₁ := eq1323519 X0
       have i₂ := eq1491293 X0 (k (k (k sF1 X0) sF1) X0)
       grind)
    | exact superpose eq1491293 eq1323519
    | (have j0 := eq1323519 (M.op x y)
       have j1 := eq1491293 X0 X0
       grind)
    | exact resolve eq1323519 eq1491293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323519
  have eq1492889 : ∀ X0 : G, (M.op x y) = (k (k (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))) X0) (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (k (k (M.op x y) X0) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1323547 x
       have i₂ := eq1491293 (k (k sF1 x) sF1) x
       grind)
    | (have i₁ := eq1323547 X0
       have i₂ := eq1491293 X0 (k (k (k sF1 X0) sF1) X0)
       grind)
    | exact superpose eq1491293 eq1323547
    | (have j0 := eq1323547 (M.op x y)
       have j1 := eq1491293 X0 X0
       grind)
    | exact resolve eq1323547 eq1491293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323547 eq1491293
  have eq1493231 : ∀ X0 : G, (M.op x y) = (k (k (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))) X0) (M.op x y)) ∨ (k (k (M.op x y) X0) (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1492889 X0
       grind)
    | (have r₁ := eq1492889 X0
       have r₂ := eq1316
       grind)
    | exact resolve eq1492889 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492889
  have eq1493232 : ∀ X0 : G, (M.op x y) = (k (k (k (σ (M.op x y)) (M.op x y)) (σ (M.op x y))) X0) ∨ (k (k (M.op x y) X0) (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1492888 X0
       grind)
    | (have r₁ := eq1492888 X0
       have r₂ := eq1316
       grind)
    | exact resolve eq1492888 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1492888
  have eq1493286 : ∀ X0 : G, (M.op x y) = (k (k (M.op x y) X0) (M.op x y)) ∨ (k (k (M.op x y) X0) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq1305041 eq1493231
    | (have j0 := eq1493231 X0
       grind)
    | exact resolve eq1493231 eq1305041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493231
  have eq1493287 : ∀ X0 : G, (k (k (M.op x y) X0) (M.op x y)) = X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1305041 eq1493232
    | (have j0 := eq1493232 X0
       grind)
    | exact resolve eq1493232 eq1305041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305041 eq1493232
  have eq1493650 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq1493287 eq108
    | (have j1 := eq1493287 (τ X0)
       grind)
    | exact resolve eq108 eq1493287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493287
  have eq1493684 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq21 eq1493650
    | (have j0 := eq1493650 X0
       grind)
    | exact resolve eq1493650 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493650
  have eq1493783 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (τ X0)) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1493684 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1493684
    | (have j0 := eq1493684 X0
       grind)
    | exact resolve eq1493684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493684
  have eq1495205 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq1493783 eq862629
    | (have j0 := eq862629 X0
       have j1 := eq1493783 X0
       grind)
    | exact resolve eq862629 eq1493783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862629 eq1493783
  have eq1495325 : ∀ X0 : G, (τ X0) = (M.op x y) ∨ (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq1495205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495205
  have eq1495518 : ∀ X0 : G, (M.op x y) = X0 ∨ (σ X0) = (k (k (σ (M.op x y)) (σ X0)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0
       have i₂ := eq1495325 (σ X0)
       grind)
    | exact superpose eq1495325 eq10
    | (have j1 := eq1495325 (σ X0)
       grind)
    | exact resolve eq10 eq1495325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495325
  have eq1495662 : ∀ X0 : G, (σ X0) = (k (σ (k (M.op x y) X0)) (σ (M.op x y))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq1495518
    | (have j0 := eq1495518 X0
       grind)
    | exact resolve eq1495518 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495518
  have eq1495679 : ∀ X0 : G, (σ X0) = (σ (k (k (M.op x y) X0) (M.op x y))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq31 eq1495662
    | (have j0 := eq1495662 X0
       grind)
    | exact resolve eq1495662 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1495662
  have eq1500456 : ∀ X0 : G, (τ (σ X0)) = (k (k (M.op x y) X0) (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq1495679 eq10
    | (have j1 := eq1495679 X0
       grind)
    | exact resolve eq10 eq1495679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495679
  have eq1500512 : ∀ X0 : G, (k (k (M.op x y) X0) (M.op x y)) = X0 ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1500456 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1500456
    | (have j0 := eq1500456 X0
       grind)
    | exact resolve eq1500456 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500456
  have eq1501393 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (k (k (M.op x y) X0) (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1493286 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493286
  have eq1501411 : ∀ X0 : G, (k (k (M.op x y) X0) (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1501393 X0
       have j1 := eq1500512 X0
       grind)
    | (have r₁ := eq1501393 (k (k (M.op x y) (M.op x y)) (M.op x y))
       have r₂ := eq1500512 (M.op x y)
       grind)
    | (have r₁ := eq1501393 X0
       have r₂ := eq1500512 X0
       grind)
    | (have r₁ := eq1501393 (M.op x y)
       have r₂ := eq1500512 (M.op x y)
       grind)
    | exact resolve eq1501393 eq1500512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1500512 eq1501393
  have eq1504592 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1501411 eq108
    | exact resolve eq108 eq1501411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq1504635 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (k (M.op x y) X0)) ∨ (M.op (M.op x y) (k (M.op x y) X0)) = X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1501411 eq14
    | (have j0 := eq14 (k (M.op x y) X0) (M.op x y)
       grind)
    | exact resolve eq14 eq1501411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1504675 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (M.op x y)) X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq1504592
    | (have j0 := eq1504592 X0
       grind)
    | exact resolve eq1504592 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504592
  have eq1505162 : ∀ X0 : G, (k (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1504675 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1504675
    | exact resolve eq1504675 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504675
  have eq1843108 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (k (M.op x y) X0)) = X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1504635 eq1754
    | (have j1 := eq1504635 X0
       grind)
    | exact resolve eq1754 eq1504635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504635
  have eq1843116 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ (M.op (M.op x y) (k (M.op x y) X0)) = X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq1843108 X0
       have i₂ := eq1258 (M.op sF0 (M.op sF0 sF0))
       grind)
    | exact superpose eq1258 eq1843108
    | (have j0 := eq1843108 X0
       grind)
    | exact resolve eq1843108 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843108
  have eq1843117 : ∀ X0 : G, (M.op (M.op x y) (k (M.op x y) X0)) = X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq1843116 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843116
  have eq1843158 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k (M.op x y) X0)) = X1 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0 X1
    first
    | exact superpose eq1843117 eq1844
    | (have j1 := eq1843117 X0
       grind)
    | exact resolve eq1844 eq1843117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1843172 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (k (M.op x y) X0) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1843117 eq1836
    | (have j1 := eq1843117 X0
       grind)
    | exact resolve eq1836 eq1843117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843117
  have eq1843190 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1195 eq1843172
    | (have j0 := eq1843172 X0
       grind)
    | exact resolve eq1843172 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843172
  have eq1843341 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 (M.op x y)) ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq1843190 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843190
  have eq1850533 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op x y)))) = (k (M.op x y) (M.op (M.op x y) X1)) ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1843158 eq1871
    | (have j1 := eq1843158 (M.op (M.op x y) X1) X1
       grind)
    | exact resolve eq1871 eq1843158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871 eq1843158
  have eq1850559 : ∀ X1 : G, (k (M.op x y) (M.op (M.op x y) X1)) = X1 ∨ (M.op x y) = (k (M.op x y) (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq1196 eq1850533
    | (have j0 := eq1850533 x X1
       grind)
    | exact resolve eq1850533 eq1196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850533
  have eq1850770 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X0) ∨ (k (M.op x y) (M.op (M.op x y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq1850559 eq1501411
    | (have j1 := eq1850559 X0
       grind)
    | exact resolve eq1501411 eq1850559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850559
  have eq1850776 : ∀ X0 : G, (k (M.op x y) (M.op (M.op x y) X0)) = X0 ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    grind
  clear eq1850770
  have eq1850812 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq1258 eq1850776
    | exact resolve eq1850776 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1850934 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1850776 eq1501411
    | (have j1 := eq1850776 X0
       grind)
    | exact resolve eq1501411 eq1850776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1850939 : ∀ X0 : G, (τ X0) = (k (τ (M.op x y)) (τ (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1850776 eq148
    | (have j1 := eq1850776 X0
       grind)
    | exact resolve eq148 eq1850776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850776
  have eq1851255 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (σ (M.op (τ X0) (M.op x y))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1850812 eq55
    | (have j1 := eq1850812 (τ X0)
       grind)
    | exact resolve eq55 eq1850812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1850812
  have eq1851586 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (σ (M.op (τ X0) (M.op x y))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21 eq1851255
    | (have j0 := eq1851255 X0
       grind)
    | exact resolve eq1851255 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851255
  have eq1852968 : ∀ X0 : G, (M.op (M.op x y) (k (M.op x y) X0)) = X0 ∨ (M.op x y) = (M.op (M.op x y) (k (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq1850934 eq1501411
    | (have j1 := eq1850934 (k (M.op x y) X0)
       grind)
    | exact resolve eq1501411 eq1850934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850934
  have eq1853286 : ∀ X0 : G, (k (σ (M.op x y)) (σ X0)) = (σ (M.op X0 (M.op x y))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1851586 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1851586
    | exact resolve eq1851586 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851586
  have eq1853318 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (σ (M.op X0 (M.op x y))) ∨ (M.op x y) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq1853286
    | (have j0 := eq1853286 X0
       grind)
    | exact resolve eq1853286 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853286
  have eq1875794 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (k (M.op x y) X0) (M.op (M.op x y) (M.op x y))) ∨ (M.op (M.op x y) (k (M.op x y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq1852968 eq1646
    | (have j1 := eq1852968 X0
       grind)
    | exact resolve eq1646 eq1852968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1875803 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op (M.op x y) (k (M.op x y) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1852968 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852968
  have eq1875817 : ∀ X0 : G, (M.op x y) = (M.op (k (M.op x y) X0) (M.op x y)) ∨ (M.op (M.op x y) (k (M.op x y) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1875794 X0
       have i₂ := eq1199 sF0
       grind)
    | exact superpose eq1199 eq1875794
    | (have j0 := eq1875794 X0
       grind)
    | exact resolve eq1875794 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875794
  have eq1876185 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (k (M.op x y) X0)) ∨ (M.op (M.op x y) (k (M.op x y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq1875817 eq1843341
    | (have j0 := eq1843341 (k (M.op x y) X0)
       have j1 := eq1875817 X0
       grind)
    | (have r₁ := eq1843341 (k (M.op x y) X0)
       have r₂ := eq1875817 X0
       grind)
    | exact resolve eq1843341 eq1875817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843341 eq1875817
  have eq1876198 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (k (M.op x y) X0)) ∨ (M.op (M.op x y) (k (M.op x y) X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq1876185 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876185
  have eq1880089 : ∀ X0 : G, (σ (k (M.op x y) (M.op x y))) = (k (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ (τ X0) = (M.op (M.op x y) (k (M.op x y) (τ X0))) := by
    intro X0
    first
    | exact superpose eq1876198 eq1306510
    | (have j1 := eq1876198 (τ X0)
       grind)
    | exact resolve eq1306510 eq1876198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306510 eq1876198
  have eq1880124 : ∀ X0 : G, (σ (k (M.op x y) (M.op x y))) = (k (k (σ (M.op x y)) (k (σ (M.op x y)) X0)) (σ (M.op x y))) ∨ (τ X0) = (M.op (M.op x y) (k (M.op x y) (τ X0))) := by
    intro X0
    first
    | exact superpose eq21 eq1880089
    | (have j0 := eq1880089 X0
       grind)
    | exact resolve eq1880089 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880089
  have eq1880151 : ∀ X0 : G, (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) X0) ∨ (τ X0) = (M.op (M.op x y) (k (M.op x y) (τ X0))) := by
    intro X0
    first
    | exact superpose eq1505162 eq1880124
    | (have j0 := eq1880124 X0
       grind)
    | exact resolve eq1880124 eq1505162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505162 eq1880124
  have eq1880154 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (τ X0) = (M.op (M.op x y) (k (M.op x y) (τ X0))) := by
    intro X0
    grind
  clear eq1880151
  have eq1880157 : ∀ X0 : G, (τ X0) = (M.op (M.op x y) (k (M.op x y) (τ X0))) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq21 eq1880154
    | (have j0 := eq1880154 X0
       grind)
    | exact resolve eq1880154 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880154
  have eq1880312 : ∀ X0 : G, (M.op (M.op x y) (k (M.op x y) X0)) = X0 ∨ (σ (M.op x y)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1880157 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1880157
    | (have j0 := eq1880157 (σ X0)
       grind)
    | exact resolve eq1880157 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880157
  have eq1880348 : ∀ X0 : G, (σ (M.op x y)) = (σ (k (M.op x y) X0)) ∨ (M.op (M.op x y) (k (M.op x y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq1880312
    | (have j0 := eq1880312 X0
       grind)
    | exact resolve eq1880312 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1880312
  have eq1881105 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op X0 (M.op x y))) ∨ (M.op x y) = X0 ∨ (M.op (M.op x y) (k (M.op x y) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq1880348 eq1853318
    | (have j0 := eq1853318 X0
       have j1 := eq1880348 X0
       grind)
    | exact resolve eq1853318 eq1880348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853318
  have eq1881233 : ∀ X0 : G, (M.op (M.op x y) (k (M.op x y) X0)) = X0 ∨ (σ (M.op x y)) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq1881105 X0
       have j1 := eq1875803 X0
       grind)
    | (have r₁ := eq1881105 X0
       have r₂ := eq1875803 X0
       grind)
    | (have r₁ := eq1881105 (M.op x y)
       have r₂ := eq1875803 (M.op x y)
       grind)
    | (have r₁ := eq1881105 (M.op x y)
       have r₂ := eq1875803 (M.op (M.op x y) (k (M.op x y) (M.op x y)))
       grind)
    | exact resolve eq1881105 eq1875803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1881105
  have eq1891226 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (k (M.op x y) X0) (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1881233 eq1836
    | (have j1 := eq1881233 X0
       grind)
    | exact resolve eq1836 eq1881233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836 eq1881233
  have eq1891234 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1195 eq1891226
    | (have j0 := eq1891226 X0
       grind)
    | exact resolve eq1891226 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq1891226
  have eq1891594 : ∀ X0 : G, (k (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ (σ (M.op x y)) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1891234 eq1501411
    | (have j1 := eq1891234 X0
       grind)
    | exact resolve eq1501411 eq1891234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501411 eq1891234
  have eq1891940 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1844 eq1891594
    | exact resolve eq1891594 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844 eq1891594
  have eq1892018 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1891940 X0
       have i₂ := eq1199 sF0
       grind)
    | exact superpose eq1199 eq1891940
    | (have j0 := eq1891940 X0
       grind)
    | exact resolve eq1891940 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891940
  have eq1892064 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (k (τ X0) (τ (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1892018 eq148
    | (have j1 := eq1892018 X0
       grind)
    | exact resolve eq148 eq1892018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892018
  have eq1938185 : ∀ X0 : G, (σ (σ (τ X0))) = (σ (k (σ (τ (M.op x y))) (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1850939 eq10707
    | (have j1 := eq1850939 X0
       grind)
    | exact resolve eq10707 eq1850939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10707 eq1850939
  have eq1938205 : ∀ X0 : G, (σ (σ (τ X0))) = (σ (k (M.op x y) (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq1938185 X0
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq1938185
    | (have j0 := eq1938185 X0
       grind)
    | exact resolve eq1938185 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938185
  have eq1938247 : ∀ X0 : G, (σ X0) = (σ (k (M.op x y) (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq1938205 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1938205
    | (have j0 := eq1938205 X0
       grind)
    | exact resolve eq1938205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938205
  have eq1946204 : ∀ X0 : G, (σ X0) = (σ (M.op x y)) ∨ (M.op (M.op x y) X0) = (M.op (M.op x y) (k (M.op x y) (M.op (M.op x y) X0))) ∨ (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq1938247 eq1880348
    | (have j0 := eq1880348 (M.op (M.op x y) X0)
       have j1 := eq1938247 X0
       grind)
    | exact resolve eq1880348 eq1938247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880348 eq1938247
  have eq1946233 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) (k (M.op x y) (M.op (M.op x y) X0))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq1946204 X0
       have j1 := eq1875803 (M.op (M.op x y) X0)
       grind)
    | (have r₁ := eq1946204 X0
       have r₂ := eq1875803 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq1946204 eq1875803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875803 eq1946204
  have eq1983409 : ∀ X0 : G, (k (M.op x y) (M.op (M.op x y) X0)) = (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1946233 eq1754
    | (have j1 := eq1946233 X0
       grind)
    | exact resolve eq1754 eq1946233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754 eq1946233
  have eq1983414 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (k (M.op x y) (M.op (M.op x y) X0)) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1343 eq1983409
    | (have j0 := eq1983409 X0
       grind)
    | exact resolve eq1983409 eq1343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343 eq1983409
  have eq1983423 : ∀ X0 : G, (k (M.op x y) (M.op (M.op x y) X0)) = X0 ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1983414 X0
       have i₂ := eq1258 (M.op sF0 (M.op X0 sF0))
       grind)
    | exact superpose eq1258 eq1983414
    | (have j0 := eq1983414 X0
       grind)
    | exact resolve eq1983414 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258 eq1983414
  have eq1983488 : ∀ X0 : G, (τ X0) = (k (τ (M.op x y)) (τ (M.op (M.op x y) X0))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1983423 eq148
    | (have j1 := eq1983423 X0
       grind)
    | exact resolve eq148 eq1983423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq1983423
  have eq1983619 : ∀ X0 : G, (τ X0) = (k (τ (M.op x y)) (k (τ X0) (τ (M.op x y)))) ∨ (σ X0) = (σ (M.op x y)) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1892064 eq1983488
    | (have j0 := eq1983488 X0
       have j1 := eq1892064 X0
       grind)
    | exact resolve eq1983488 eq1892064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892064 eq1983488
  have eq1983673 : ∀ X0 : G, (τ X0) = (k (τ (M.op x y)) (k (τ X0) (τ (M.op x y)))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq1983619 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983619
  have eq2049310 : ∀ X0 : G, (σ (σ (τ (τ X0)))) = (k (σ (σ (τ (M.op x y)))) (k X0 (σ (M.op x y)))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1983673 eq1308465
    | (have j1 := eq1983673 (τ X0)
       grind)
    | exact resolve eq1308465 eq1983673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308465 eq1983673
  have eq2049345 : ∀ X0 : G, (σ (σ (τ (τ X0)))) = (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2049310 X0
       have i₂ := eq11 sF0
       grind)
    | exact superpose eq11 eq2049310
    | (have j0 := eq2049310 X0
       grind)
    | exact resolve eq2049310 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049310
  have eq2049370 : ∀ X0 : G, (σ (σ (τ (τ X0)))) = (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq2049345
    | (have j0 := eq2049345 X0
       grind)
    | exact resolve eq2049345 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2049345
  have eq2049385 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2049370 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq2049370
    | (have j0 := eq2049370 X0
       grind)
    | exact resolve eq2049370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049370
  have eq2049394 : ∀ X0 : G, (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq2049385 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2049385
    | (have j0 := eq2049385 X0
       grind)
    | exact resolve eq2049385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049385
  have eq2049397 : ∀ X0 : G, (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2049394 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2049394
    | (have j0 := eq2049394 X0
       grind)
    | exact resolve eq2049394 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2049394
  have eq2049447 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) := by
    first
    | exact superpose eq2049397 eq115211
    | (have j1 := eq2049397 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y)))
       grind)
    | exact resolve eq115211 eq2049397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115211 eq2049397
  have eq2049507 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op x y))) := by grind
  clear eq2049447
  have eq2049612 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2049507 eq1196
    | exact resolve eq1196 eq2049507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1196 eq2049507
  have eq2049773 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq2049612
       have i₂ := eq1199 sF1
       grind)
    | exact superpose eq1199 eq2049612
    | exact resolve eq2049612 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq2049612
  have eq2050900 : False := by grind
  exact eq2050900

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyy_pxy_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq78 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
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
  have eq90 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X1
    first
    | exact superpose eq81 eq53
    | exact resolve eq53 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 x) (M.op x x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq101 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq78 eq12
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | exact superpose eq64 eq100
    | exact resolve eq100 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq100
  have eq142 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq90 eq12
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq177 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq199 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq177
    | (have j0 := eq177 X0 X1
       grind)
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq200 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq158 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq158
    | exact resolve eq158 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq307 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) ∨ (k X1 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op x x)
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq308 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq308 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq308 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq317 : ∀ X0 : G, (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq200 X0 X0
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq200
    | exact resolve eq200 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq309 (σ X0)
       grind)
    | exact superpose eq309 eq15
    | exact resolve eq15 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq320 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq319 X0
       have i₂ := eq309 X0
       grind)
    | exact superpose eq309 eq319
    | exact resolve eq319 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq322 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq317 X0
       have i₂ := eq309 (τ X0)
       grind)
    | exact superpose eq309 eq317
    | exact resolve eq317 eq309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq317
  have eq364 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X2 X0)) X0
       have i₂ := eq82 X0 X1 X2
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq28516 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq307 x (M.op X0 x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq307
    | (have j0 := eq307 X0 (M.op X1 X0)
       grind)
    | (have r₁ := eq307 x (M.op X0 x)
       have r₂ := eq53 X0 x x
       grind)
    | exact resolve eq307 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28521 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq90 eq307
    | (have j0 := eq307 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq307 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq90 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq307 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq28522 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq78 eq307
    | (have j0 := eq307 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq307 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq78 (σ y)
       grind)
    | exact resolve eq307 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq307
  have eq28523 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by grind
  clear eq28522
  have eq28524 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by grind
  clear eq28521
  have eq28527 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28516 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28516
  have eq28530 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have j1 := eq101 (σ y)
       grind)
    | (have r₁ := eq28523
       have r₂ := eq101 (σ y)
       grind)
    | exact resolve eq28523 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq28523
  have eq28531 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have j1 := eq142 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq28524
       have r₂ := eq142 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq28524 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq28524
  have eq28535 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq28527 X0 X1
       have j1 := eq94 X0 X1 X0
       grind)
    | (have r₁ := eq28527 x X1
       have r₂ := eq94 x X1 x
       grind)
    | exact resolve eq28527 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq28527
  have eq28563 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq28530 eq200
    | exact resolve eq200 eq28530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28566 : (τ (σ y)) = (k (τ (M.op (σ x) (σ y))) (M.op (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq28563
       have i₂ := eq322 sF3
       grind)
    | exact superpose eq322 eq28563
    | exact resolve eq28563 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28563
  have eq28570 : y = (k (τ (M.op (σ x) (σ y))) (M.op y y)) := by
    first
    | exact superpose eq39 eq28566
    | exact resolve eq28566 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28566
  have eq28605 : (τ (M.op (σ x) (σ y))) = (k (τ (σ x)) (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq28531 eq200
    | exact resolve eq200 eq28531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq28531
  have eq28608 : (τ (M.op (σ x) (σ y))) = (k (τ (σ x)) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq28605
       have i₂ := eq322 sF4
       grind)
    | exact superpose eq322 eq28605
    | exact resolve eq28605 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28605
  have eq28613 : (τ (M.op (σ x) (σ y))) = (k x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq38 eq28608
    | exact resolve eq28608 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28608
  have eq28730 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28535 (M.op X0 X0) X1
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq28535
    | exact resolve eq28535 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28535
  have eq28804 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = (k (M.op X2 (M.op (τ X0) X1)) X1) ∨ (k X0 (σ X1)) = X0 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28730 X1 X1
       have i₂ := eq199 X0 X1
       grind)
    | (have i₁ := eq28730 (τ X0) X1
       have i₂ := eq199 X0 (τ X0)
       grind)
    | exact superpose eq199 eq28730
    | (have j1 := eq199 X0 X1
       grind)
    | exact resolve eq28730 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq28730
  have eq28862 : ∀ X0 X1 X2 : G, (M.op (τ X0) X1) = (k (M.op X2 (M.op (τ X0) X1)) X1) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq28804 X0 X1 X2
       have j1 := eq364 (τ X0) X1 X2
       grind)
    | (have r₁ := eq28804 X0 X1 X2
       have r₂ := eq364 (τ X0) X1 X2
       grind)
    | exact resolve eq28804 eq364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq28804
  have eq214550 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28862 X0 X1 (M.op x (τ X0))
       have i₂ := eq53 x (τ X0) X1
       grind)
    | exact superpose eq53 eq28862
    | (have j0 := eq28862 X0 X1 x
       grind)
    | exact resolve eq28862 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28862
  have eq214559 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq38 eq214550
    | (have j0 := eq214550 (σ x) X0
       grind)
    | exact resolve eq214550 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214578 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq28570
       have i₂ := eq214550 sF4 (M.op y y)
       grind)
    | exact superpose eq214550 eq28570
    | (have j1 := eq214550 (M.op (σ x) (σ y)) (M.op y y)
       grind)
    | exact resolve eq28570 eq214550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28570 eq214550
  have eq214636 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) := by
    first
    | (have i₁ := eq214578
       have i₂ := eq320 y
       grind)
    | exact superpose eq320 eq214578
    | exact resolve eq214578 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320 eq214578
  have eq214649 : ∀ X0 : G, (σ x) = (σ (k x X0)) ∨ (k x X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq31 eq214559
    | (have j0 := eq214559 X0
       grind)
    | exact resolve eq214559 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq214559
  have eq214671 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) := by
    first
    | (have i₁ := eq214636
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq214636
    | exact resolve eq214636 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq214636
  have eq214683 : y = (M.op (τ (M.op (σ x) (σ y))) (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28530 eq214671
    | exact resolve eq214671 eq28530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28530 eq214671
  have eq214700 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq214683 eq53
    | exact resolve eq53 eq214683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214702 : ∀ X0 : G, y = (M.op (τ (M.op (σ x) (σ y))) (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq214683 eq54
    | exact resolve eq54 eq214683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214683
  have eq216570 : (σ x) = (σ (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq28613 eq214649
    | exact resolve eq214649 eq28613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28613
  have eq216983 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq216570
       have i₂ := eq11 sF4
       grind)
    | exact superpose eq11 eq216570
    | exact resolve eq216570 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216570
  have eq218113 : ∀ X0 : G, x = (M.op (M.op X0 x) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq216983 eq53
    | exact resolve eq53 eq216983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq216983
  have eq218126 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq218113 eq214700
    | exact resolve eq214700 eq218113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214700 eq218113
  have eq218140 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq218126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq218126
    | exact resolve eq218126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218126
  have eq218648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq218140 eq11
    | exact resolve eq11 eq218140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218140
  have eq219015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq218648
    | exact resolve eq218648 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218648
  have eq219020 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq219015
       have r₂ := eq27
       grind)
    | exact resolve eq219015 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219015
  have eq219021 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq219020 eq27
    | exact resolve eq27 eq219020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219027 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq219020 eq102
    | (have r₁ := eq102
       have r₂ := eq219020
       grind)
    | exact resolve eq102 eq219020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq219041 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq219020
  have eq219043 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq219027
  have eq219074 : (σ x) = (σ y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq214649 y
       have i₂ := eq219043
       grind)
    | exact superpose eq219043 eq214649
    | (have j0 := eq214649 y
       grind)
    | exact resolve eq214649 eq219043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214649
  have eq219324 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq219074
       have r₂ := eq219041
       grind)
    | exact resolve eq219074 eq219041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219041 eq219074
  have eq219351 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq219324
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq219324
    | exact resolve eq219324 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219324
  have eq219678 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq219043
       have i₂ := eq219351
       grind)
    | exact superpose eq219351 eq219043
    | exact resolve eq219043 eq219351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219043 eq219351
  have eq219721 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq219678
  have eq219743 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq219721
    | exact resolve eq219721 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219721
  have eq219767 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq219743
       have r₂ := eq219021
       grind)
    | exact resolve eq219743 eq219021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219021 eq219743
  have eq219791 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq219767 eq27
    | exact resolve eq27 eq219767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq219793 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq219767 eq81
    | exact resolve eq81 eq219767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq220125 : ∀ X0 : G, (σ x) = (σ y) ∨ y = (M.op (τ (M.op (σ x) (σ y))) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq219767 eq214702
    | (have j0 := eq214702 X0
       grind)
    | exact resolve eq214702 eq219767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214702
  have eq220439 : ∀ X0 : G, y = (M.op (τ (σ x)) (M.op y X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq219767 eq220125
    | exact resolve eq220125 eq219767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219767 eq220125
  have eq220773 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq38 eq220439
    | exact resolve eq220439 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220439
  have eq221050 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq219793 eq219793
    | exact resolve eq219793 eq219793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219793
  have eq223558 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq221050 eq322
    | exact resolve eq322 eq221050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq221050
  have eq223676 : x = (M.op x x) := by
    first
    | exact superpose eq38 eq223558
    | exact resolve eq223558 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223558
  have eq224563 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq54 x x x
       have i₂ := eq223676
       grind)
    | exact superpose eq223676 eq54
    | exact resolve eq54 eq223676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq234123 : x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq224563 (M.op y x)
       have i₂ := eq220773 x
       grind)
    | exact superpose eq220773 eq224563
    | exact resolve eq224563 eq220773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220773 eq224563
  have eq234143 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq234123
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq234123
    | exact resolve eq234123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234123
  have eq234147 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq234143 eq39
    | exact resolve eq39 eq234143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq234143
  have eq234363 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq38 eq234147
    | exact resolve eq234147 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq234147
  have eq234388 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq234363 eq20
    | exact resolve eq20 eq234363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234363
  have eq234677 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq234388
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq234388
    | exact resolve eq234388 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234388
  have eq234680 : x = y := by
    first
    | (have r₁ := eq234677
       have r₂ := eq219791
       grind)
    | exact resolve eq234677 eq219791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234677
  have eq234681 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq234680
       grind)
    | exact superpose eq234680 eq18
    | exact resolve eq18 eq234680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq234680
  have eq254648 : x = (M.op x y) := by
    first
    | (have i₁ := eq234681
       have i₂ := eq223676
       grind)
    | exact superpose eq223676 eq234681
    | exact resolve eq234681 eq223676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223676 eq234681
  have eq260289 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq254648 eq20
    | exact resolve eq20 eq254648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq254648
  have eq273873 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq260289
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq260289
    | exact resolve eq260289 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq260289
  have eq274409 : False := by grind
  exact eq274409

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(X,Y) then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pyx_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
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
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  clear eq18
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
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq139
    | exact resolve eq139 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq189 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq211 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189
    | (have j0 := eq189 X0 X1
       grind)
    | exact resolve eq189 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq215 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq10
    | exact resolve eq10 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq28
    | exact resolve eq28 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq223 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq36
    | exact resolve eq36 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq261 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq215 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215
    | exact resolve eq215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1341 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq218 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq218
    | (have j0 := eq218 x
       grind)
    | exact resolve eq218 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq2062 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq223
    | (have j0 := eq223 (M.op x y)
       grind)
    | exact resolve eq223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq5370 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X0 X1
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X0 X1
       grind)
    | (have r₁ := eq94 x x x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq5371 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5370 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5370
  have eq5375 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq5376 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq5382 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5376
  have eq5383 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5375
  have eq5388 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5382 eq1341
    | exact resolve eq1341 eq5382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1341 eq5382
  have eq5391 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5383 eq2062
    | exact resolve eq2062 eq5383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062 eq5383
  have eq5392 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5388
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5388
    | exact resolve eq5388 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5388
  have eq5395 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5391
    | exact resolve eq5391 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5391
  have eq11474 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (M.op (τ X0) (τ X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = X0 ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq211 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X0)
       have i₂ := eq211 X0 X1
       grind)
    | exact superpose eq211 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq211 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) X1
       have r₂ := eq211 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq211 X0 (τ X0)
       grind)
    | (have r₁ := eq13 X1 (τ X0)
       have r₂ := eq211 X0 X1
       grind)
    | exact resolve eq13 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq11563 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (M.op (τ X0) (τ X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11474 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11474
  have eq11564 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) (τ X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11563 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11563
  have eq355364 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (σ X0) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11564 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11564
    | (have j0 := eq11564 (σ X0) X1
       grind)
    | exact resolve eq11564 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11564
  have eq355371 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq355364 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq355364
    | (have j0 := eq355364 X0 X1
       grind)
    | exact resolve eq355364 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355364
  have eq356010 : (σ (σ (M.op x y))) = (σ (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5392 eq355371
    | (have j0 := eq355371 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq355371 eq5392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5392
  have eq356011 : (σ (σ (M.op x y))) = (σ (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq5395 eq355371
    | (have j0 := eq355371 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq355371 eq5395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355371
  have eq356025 : (σ (σ (M.op x y))) = (σ (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq356011
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq356011
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq356011
    | exact resolve eq356011 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356011
  have eq356026 : (σ (σ (M.op x y))) = (σ (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq356010
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq356010
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq356010
    | exact resolve eq356010 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356010
  have eq356033 : (σ y) = (τ (σ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq356025 eq10
    | exact resolve eq10 eq356025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356025
  have eq356051 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq356033
       have i₂ := eq10 sF1
       grind)
    | exact superpose eq10 eq356033
    | exact resolve eq356033 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356033
  have eq356061 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq356051 eq53
    | exact resolve eq53 eq356051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356104 : ∀ X0 : G, (τ (σ (M.op x y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq356061 eq261
    | (have j1 := eq356061 X0
       grind)
    | exact resolve eq261 eq356061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq356061
  have eq356130 : ∀ X0 : G, (τ (σ (M.op x y))) = (M.op y y) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq39 eq356104
    | (have j0 := eq356104 X0
       grind)
    | exact resolve eq356104 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356104
  have eq356150 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq37 eq356130
    | (have j0 := eq356130 X0
       grind)
    | exact resolve eq356130 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356130
  have eq356239 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq356150 eq53
    | exact resolve eq53 eq356150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq356150
  have eq356343 : (σ x) = (τ (σ (σ (M.op x y)))) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq356026 eq10
    | exact resolve eq10 eq356026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356026
  have eq356361 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq356343
       have i₂ := eq10 sF1
       grind)
    | exact superpose eq10 eq356343
    | exact resolve eq356343 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356343
  have eq356373 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq356361 eq356239
    | exact resolve eq356239 eq356361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq356373
    | exact resolve eq356373 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356373
  have eq356393 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq356384
       have r₂ := eq27
       grind)
    | exact resolve eq356384 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356384
  have eq356730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq356393 eq356239
    | exact resolve eq356239 eq356393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356239 eq356393
  have eq356836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq356730
  have eq356914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq356836
    | exact resolve eq356836 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356836
  have eq356977 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq356914
       have r₂ := eq27
       grind)
    | exact resolve eq356914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356914
  have eq357030 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq356977
       grind)
    | exact superpose eq356977 eq140
    | exact resolve eq140 eq356977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356977
  have eq357175 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq357030
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq357030
    | exact resolve eq357030 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357030
  have eq357209 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq357175
    | exact resolve eq357175 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357175
  have eq357651 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq357209 eq82
    | exact resolve eq82 eq357209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357209
  have eq359279 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq356361 eq357651
    | exact resolve eq357651 eq356361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq359279
  have eq359334 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq359325
    | exact resolve eq359325 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359325
  have eq359336 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq359334
       have r₂ := eq27
       grind)
    | exact resolve eq359334 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359334
  have eq359388 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq359336 eq357651
    | exact resolve eq357651 eq359336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357651 eq359336
  have eq359494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq359388
  have eq359576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq359494
    | exact resolve eq359494 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359494
  have eq359636 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq359576
       have r₂ := eq27
       grind)
    | exact resolve eq359576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359576
  have eq359660 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq359636 eq39
    | exact resolve eq39 eq359636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq359636
  have eq360220 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq359660
    | exact resolve eq359660 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359660
  have eq360228 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq360220 eq38
    | exact resolve eq38 eq360220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360220
  have eq360787 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq360228
    | exact resolve eq360228 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360228
  have eq360791 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq360787 eq20
    | exact resolve eq20 eq360787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360792 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq360787 eq77
    | exact resolve eq77 eq360787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq361686 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq361691 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq360791
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq360791
    | exact resolve eq360791 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360791
  have eq363607 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq360792 (M.op y x)
       have i₂ := eq360792 x
       grind)
    | exact superpose eq360792 eq360792
    | exact resolve eq360792 eq360792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360792
  have eq363627 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq363607
  have eq363680 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq363627
       grind)
    | exact superpose eq363627 eq140
    | exact resolve eq140 eq363627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363627
  have eq363826 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq363680
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq363680
    | exact resolve eq363680 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363680
  have eq363905 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq361691 eq363826
    | exact resolve eq363826 eq361691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361691 eq363826
  have eq364074 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq363905
  have eq364248 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq364074 eq5395
    | exact resolve eq5395 eq364074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5395
  have eq364487 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq364248
    | exact resolve eq364248 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq364248
  have eq365003 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq360787 eq364487
    | exact resolve eq364487 eq360787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360787 eq364487
  have eq365663 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq365003
       have r₂ := eq361686
       grind)
    | exact resolve eq365003 eq361686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361686 eq365003
  have eq365729 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq365663
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq365663
    | exact resolve eq365663 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365663
  have eq365751 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq365729
       have i₂ := eq140 y
       grind)
    | exact superpose eq140 eq365729
    | exact resolve eq365729 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365729
  have eq365754 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq365751
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq365751
    | exact resolve eq365751 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq365751
  have eq365895 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq365754 eq82
    | exact resolve eq82 eq365754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq365754
  have eq371589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq356361 eq365895
    | exact resolve eq365895 eq356361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356361 eq365895
  have eq371660 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq371589
    | exact resolve eq371589 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371589
  have eq371662 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq371660
       have r₂ := eq27
       grind)
    | exact resolve eq371660 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371660
  have eq387140 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq371662 eq364074
    | exact resolve eq364074 eq371662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364074 eq371662
  have eq387271 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq387140
  have eq387346 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq387271 eq38
    | exact resolve eq38 eq387271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq387271
  have eq387840 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq387346
    | exact resolve eq387346 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq387346
  have eq387841 : x = (M.op x y) := by grind
  clear eq387840
  have eq387846 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq387841 eq20
    | exact resolve eq20 eq387841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq387855 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq387841 eq80
    | exact resolve eq80 eq387841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq387841
  have eq409045 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq387846
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq387846
    | exact resolve eq387846 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387846
  have eq409563 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq409045 eq22
    | exact resolve eq22 eq409045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq409564 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq409045 eq26
    | exact resolve eq26 eq409045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq409045
  have eq425682 : x = (M.op x x) := by
    first
    | (have i₁ := eq387855 (M.op x x)
       have i₂ := eq387855 x
       grind)
    | exact superpose eq387855 eq387855
    | exact resolve eq387855 eq387855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387855
  have eq426642 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq140 x
       have i₂ := eq425682
       grind)
    | exact superpose eq425682 eq140
    | exact resolve eq140 eq425682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq425682
  have eq426841 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq426642
       have i₂ := eq409563
       grind)
    | exact superpose eq409563 eq426642
    | exact resolve eq426642 eq409563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409563 eq426642
  have eq426904 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq426841 eq356051
    | exact resolve eq356051 eq426841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356051
  have eq427392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq409564 eq426904
    | exact resolve eq426904 eq409564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426904
  have eq427432 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq427392
       have r₂ := eq27
       grind)
    | exact resolve eq427392 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427392
  have eq436965 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq427432 eq5371
    | exact resolve eq5371 eq427432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5371 eq427432
  have eq436977 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq436965
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq436965
    | exact resolve eq436965 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq436965
  have eq437039 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq426841 eq436977
    | exact resolve eq436977 eq426841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436977
  have eq437040 : (σ (M.op x y)) = (σ y) := by grind
  clear eq437039
  have eq442321 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq437040 eq409564
    | exact resolve eq409564 eq437040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409564 eq437040
  have eq443078 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq426841 eq442321
    | exact resolve eq442321 eq426841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426841 eq442321
  have eq443339 : False := by grind
  exact eq443339

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyy_pyx_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
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
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
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
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
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
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq97 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq59 eq97
    | exact resolve eq97 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq97
  have eq121 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq137 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq137
    | exact resolve eq137 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq216 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq28
    | exact resolve eq28 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq221 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq36
    | exact resolve eq36 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (k (σ y) (σ X0)) = (σ (k y (k X0 X1))) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (k X0 X1)
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq36
    | (have j1 := eq121 X0 X1
       grind)
    | exact resolve eq36 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq386 : ∀ X0 X1 : G, (σ (k y X0)) = (σ (k y (k X0 X1))) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq36 eq384
    | (have j0 := eq384 X0 X1
       grind)
    | exact resolve eq384 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq384
  have eq1325 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq216 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq216
    | (have j0 := eq216 x
       grind)
    | exact resolve eq216 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq1358 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1325 eq14
    | (have j0 := eq14 (M.op (σ x) (σ x)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1359 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1358
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1358
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq1358
    | exact resolve eq1358 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1363 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq1359
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1359
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq1359
    | exact resolve eq1359 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq2070 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq221
    | (have j0 := eq221 (M.op x y)
       grind)
    | exact resolve eq221 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2130 : (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ y) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2070 eq14
    | (have j0 := eq14 (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)
       grind)
    | exact resolve eq14 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2131 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq2130
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2130
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2130
    | exact resolve eq2130 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq2135 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq2131
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2131
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2131
    | exact resolve eq2131 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq5621 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X0 X1
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X0 X1
       grind)
    | (have r₁ := eq94 x x x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq5622 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5621 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5621
  have eq5626 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq5627 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq5633 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5627
  have eq5634 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5626
  have eq5638 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5633 eq1363
    | exact resolve eq1363 eq5633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363 eq5633
  have eq5641 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5634 eq2135
    | exact resolve eq2135 eq5634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135
  have eq5642 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5634 eq2070
    | exact resolve eq2070 eq5634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070 eq5634
  have eq5644 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5638
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5638
    | exact resolve eq5638 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5638
  have eq5646 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5642
    | exact resolve eq5642 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5642
  have eq5647 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq5641
    | exact resolve eq5641 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5641
  have eq11049 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5644 eq53
    | exact resolve eq53 eq5644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5644
  have eq11062 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq5647 eq53
    | exact resolve eq53 eq5647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq12034 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11062 eq11049
    | exact resolve eq11049 eq11062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11062
  have eq12107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq12034
    | exact resolve eq12034 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12034
  have eq12112 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12107
       have r₂ := eq27
       grind)
    | exact resolve eq12107 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12107
  have eq12148 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12112 eq5622
    | exact resolve eq5622 eq12112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12112
  have eq12154 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12148
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq12148
    | exact resolve eq12148 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12148
  have eq12194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12154 eq11049
    | exact resolve eq11049 eq12154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12223 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12154
  have eq12226 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12194
  have eq12238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12226
       have r₂ := eq12223
       grind)
    | exact resolve eq12226 eq12223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12223 eq12226
  have eq12250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq12238
    | exact resolve eq12238 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12238
  have eq12251 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12250
       have r₂ := eq27
       grind)
    | exact resolve eq12250 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12250
  have eq12261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12251 eq5647
    | exact resolve eq5647 eq12251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5647
  have eq12288 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12251 eq5622
    | exact resolve eq5622 eq12251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12293 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq12261
  have eq12296 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12288
       have i₂ := eq100 sF2
       grind)
    | exact superpose eq100 eq12288
    | exact resolve eq12288 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12288
  have eq12304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq12293
    | exact resolve eq12293 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12293
  have eq12316 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq12304
       have r₂ := eq27
       grind)
    | exact resolve eq12304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12304
  have eq12955 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12316 eq5622
    | exact resolve eq5622 eq12316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12316
  have eq12961 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12955
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq12955
    | exact resolve eq12955 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12955
  have eq13102 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12961 eq12251
    | exact resolve eq12251 eq12961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12251 eq12961
  have eq13135 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13102
  have eq13160 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13135 eq26
    | exact resolve eq26 eq13135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13164 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13135 eq39
    | exact resolve eq39 eq13135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13135
  have eq13221 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq38 eq13164
    | exact resolve eq13164 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13164
  have eq13230 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq13221 eq39
    | exact resolve eq39 eq13221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13221
  have eq13277 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq37 eq13230
    | exact resolve eq13230 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13230
  have eq13285 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13277 eq38
    | exact resolve eq38 eq13277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13277
  have eq13333 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq37 eq13285
    | exact resolve eq13285 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13285
  have eq14156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13160 eq12296
    | exact resolve eq12296 eq13160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12296 eq13160
  have eq14190 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14156
  have eq14202 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq14190
       have r₂ := eq27
       grind)
    | exact resolve eq14190 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14190
  have eq14210 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14202 eq39
    | exact resolve eq39 eq14202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq14202
  have eq14257 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq14210
    | exact resolve eq14210 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14210
  have eq14265 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14257 eq38
    | exact resolve eq38 eq14257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14257
  have eq14313 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq14265
    | exact resolve eq14265 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14265
  have eq14317 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14313 eq20
    | exact resolve eq20 eq14313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14318 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14313 eq77
    | exact resolve eq77 eq14313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq14344 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq14313
  have eq14345 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14317
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14317
    | exact resolve eq14317 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14317
  have eq15458 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14318 (M.op y x)
       have i₂ := eq14318 x
       grind)
    | exact superpose eq14318 eq14318
    | exact resolve eq14318 eq14318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14318
  have eq15471 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq15458
  have eq15494 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138 y
       have i₂ := eq15471
       grind)
    | exact superpose eq15471 eq138
    | exact resolve eq138 eq15471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15471
  have eq15524 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15494
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15494
    | exact resolve eq15494 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15494
  have eq15527 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14345 eq15524
    | exact resolve eq15524 eq14345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15524
  have eq15587 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq15527
  have eq15640 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15587 eq5646
    | exact resolve eq5646 eq15587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5646 eq15587
  have eq15697 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq15640
    | exact resolve eq15640 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq15640
  have eq17781 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13333 eq15697
    | exact resolve eq15697 eq13333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13333 eq15697
  have eq17825 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq17781
  have eq17858 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17825
       have r₂ := eq14344
       grind)
    | exact resolve eq17825 eq14344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14344 eq17825
  have eq17860 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17858
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq17858
    | exact resolve eq17858 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17858
  have eq17862 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17860
       have i₂ := eq138 y
       grind)
    | exact superpose eq138 eq17860
    | exact resolve eq17860 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17860
  have eq17864 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17862
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17862
    | exact resolve eq17862 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17862
  have eq17908 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17864 eq5622
    | exact resolve eq5622 eq17864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17864
  have eq17918 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17908
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq17908
    | exact resolve eq17908 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17908
  have eq17970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17918 eq11049
    | exact resolve eq11049 eq17918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11049 eq17918
  have eq18015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17970
    | exact resolve eq17970 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17970
  have eq18027 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18015
       have r₂ := eq27
       grind)
    | exact resolve eq18015 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18015
  have eq18215 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18027 eq14345
    | exact resolve eq14345 eq18027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14345 eq18027
  have eq18222 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq18215
  have eq18239 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18222 eq38
    | exact resolve eq38 eq18222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq18222
  have eq18291 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq18239
    | exact resolve eq18239 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq18239
  have eq18292 : x = (M.op x y) := by grind
  clear eq18291
  have eq18297 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18292 eq20
    | exact resolve eq20 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq18306 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq18292 eq80
    | exact resolve eq80 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq18309 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq18292 eq95
    | exact resolve eq95 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq20024 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq18292 eq18309
    | exact resolve eq18309 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18292 eq18309
  have eq20027 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18297
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18297
    | exact resolve eq18297 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18297
  have eq20119 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20027 eq22
    | exact resolve eq22 eq20027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq20120 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20027 eq26
    | exact resolve eq26 eq20027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq20128 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq20027 eq104
    | exact resolve eq104 eq20027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq20027
  have eq21465 : x = (M.op x x) := by
    first
    | (have i₁ := eq18306 (M.op x x)
       have i₂ := eq18306 x
       grind)
    | exact superpose eq18306 eq18306
    | exact resolve eq18306 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18306
  have eq21573 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq20024
       have i₂ := eq21465
       grind)
    | exact superpose eq21465 eq20024
    | (have r₁ := eq20024
       have r₂ := eq21465
       grind)
    | exact resolve eq20024 eq21465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20024
  have eq21584 : x = (k y x) := by grind
  clear eq21573
  have eq21598 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq20128
       have i₂ := eq21584
       grind)
    | exact superpose eq21584 eq20128
    | exact resolve eq20128 eq21584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20128
  have eq21615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq21598
       have i₂ := eq20119
       grind)
    | exact superpose eq20119 eq21598
    | exact resolve eq21598 eq20119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21598
  have eq21631 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq21615
       have r₂ := eq27
       grind)
    | exact resolve eq21615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21615
  have eq21638 : (σ (k y x)) = (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq386 y x
       have i₂ := eq21584
       grind)
    | exact superpose eq21584 eq386
    | (have j0 := eq386 x y
       grind)
    | exact resolve eq386 eq21584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq21648 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21638
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq21638
    | exact resolve eq21638 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21638
  have eq21655 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21648
       have i₂ := eq138 y
       grind)
    | exact superpose eq138 eq21648
    | exact resolve eq21648 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21648
  have eq21661 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21655
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21655
    | exact resolve eq21655 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21655
  have eq21666 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21661
       have i₂ := eq21584
       grind)
    | exact superpose eq21584 eq21661
    | exact resolve eq21661 eq21584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21584 eq21661
  have eq21671 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21666
       have i₂ := eq20119
       grind)
    | exact superpose eq20119 eq21666
    | exact resolve eq21666 eq20119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21666
  have eq21675 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21671
       have i₂ := eq20119
       grind)
    | exact superpose eq20119 eq21671
    | exact resolve eq21671 eq20119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21671
  have eq21678 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21675
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21675
    | exact resolve eq21675 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21675
  have eq21679 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21678
       have i₂ := eq20119
       grind)
    | exact superpose eq20119 eq21678
    | exact resolve eq21678 eq20119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21678
  have eq21680 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21679
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21679
    | exact resolve eq21679 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq21679
  have eq21681 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20120 eq21680
    | exact resolve eq21680 eq20120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21680
  have eq21682 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq21681
       have r₂ := eq21631
       grind)
    | exact resolve eq21681 eq21631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21631 eq21681
  have eq21706 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq138 x
       have i₂ := eq21465
       grind)
    | exact superpose eq21465 eq138
    | exact resolve eq138 eq21465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq21465
  have eq21771 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq21706
       have i₂ := eq20119
       grind)
    | exact superpose eq20119 eq21706
    | exact resolve eq21706 eq20119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20119 eq21706
  have eq21953 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21771 eq21682
    | exact resolve eq21682 eq21771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21682
  have eq21956 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq21953
  have eq22474 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21956 eq5622
    | exact resolve eq5622 eq21956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5622 eq21956
  have eq22481 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22474
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq22474
    | exact resolve eq22474 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq22474
  have eq22537 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21771 eq22481
    | exact resolve eq22481 eq21771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22481
  have eq23037 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22537 eq20120
    | exact resolve eq20120 eq22537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20120 eq22537
  have eq23343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21771 eq23037
    | exact resolve eq23037 eq21771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21771 eq23037
  have eq23397 : False := by grind
  exact eq23397

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyy_pyx_pxy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
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
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
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
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
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
  have eq83 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq77 eq53
    | exact resolve eq53 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (M.op X0 X2) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op x x) (M.op X0 x)
       have i₂ := eq53 X0 x x
       grind)
    | exact superpose eq53 eq12
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq97 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq59 eq97
    | exact resolve eq97 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq97
  have eq121 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq137 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq137 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq137
    | exact resolve eq137 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq216 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq28
    | exact resolve eq28 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq221 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq36
    | exact resolve eq36 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq384 : ∀ X0 X1 : G, (k (σ y) (σ X0)) = (σ (k y (k X0 X1))) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 (k X0 X1)
       have i₂ := eq121 X0 X1
       grind)
    | exact superpose eq121 eq36
    | (have j1 := eq121 X0 X1
       grind)
    | exact resolve eq36 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq386 : ∀ X0 X1 : G, (σ (k y X0)) = (σ (k y (k X0 X1))) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | exact superpose eq36 eq384
    | (have j0 := eq384 X0 X1
       grind)
    | exact resolve eq384 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq384
  have eq1325 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq216 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq216
    | (have j0 := eq216 x
       grind)
    | exact resolve eq216 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq1358 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1325 eq14
    | (have j0 := eq14 (M.op (σ x) (σ x)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1359 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) ∨ (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1358
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1358
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq1358
    | exact resolve eq1358 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq1363 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq1359
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq1359
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq1359
    | exact resolve eq1359 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359
  have eq2070 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq221
    | (have j0 := eq221 (M.op x y)
       grind)
    | exact resolve eq221 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2130 : (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ y) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | exact superpose eq2070 eq14
    | (have j0 := eq14 (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)
       grind)
    | exact resolve eq14 eq2070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2131 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq2130
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2130
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2130
    | exact resolve eq2130 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq2135 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq2131
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2131
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2131
    | exact resolve eq2131 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq5621 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X0 X1
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X0 X1
       grind)
    | (have r₁ := eq94 x x x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq5622 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5621 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5621
  have eq5626 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq5627 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq5633 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5627
  have eq5634 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5626
  have eq5638 : (σ x) = (σ (M.op x y)) ∨ (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5633 eq1363
    | exact resolve eq1363 eq5633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363 eq5633
  have eq5641 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq5634 eq2135
    | exact resolve eq2135 eq5634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135
  have eq5642 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5634 eq2070
    | exact resolve eq2070 eq5634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070 eq5634
  have eq5644 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq5638
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5638
    | exact resolve eq5638 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5638
  have eq5646 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5642
    | exact resolve eq5642 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5642
  have eq5647 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq5641
    | exact resolve eq5641 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5641
  have eq11221 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq5644 eq53
    | exact resolve eq53 eq5644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5644
  have eq11234 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq5647 eq53
    | exact resolve eq53 eq5647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq12209 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11234 eq11221
    | exact resolve eq11221 eq11234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11234
  have eq12281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq12209
    | exact resolve eq12209 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12209
  have eq12286 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12281
       have r₂ := eq27
       grind)
    | exact resolve eq12281 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12281
  have eq12321 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12286 eq5622
    | exact resolve eq5622 eq12286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12286
  have eq12327 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12321
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq12321
    | exact resolve eq12321 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12321
  have eq12367 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12327 eq11221
    | exact resolve eq11221 eq12327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12395 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12327
  have eq12398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12367
  have eq12410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12398
       have r₂ := eq12395
       grind)
    | exact resolve eq12398 eq12395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12395 eq12398
  have eq12422 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq12410
    | exact resolve eq12410 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12410
  have eq12423 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12422
       have r₂ := eq27
       grind)
    | exact resolve eq12422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12422
  have eq12433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12423 eq5647
    | exact resolve eq5647 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5647
  have eq12459 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12423 eq5622
    | exact resolve eq5622 eq12423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq12433
  have eq12467 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12459
       have i₂ := eq100 sF2
       grind)
    | exact superpose eq100 eq12459
    | exact resolve eq12459 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12459
  have eq12475 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq12464
    | exact resolve eq12464 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12464
  have eq12487 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq12475
       have r₂ := eq27
       grind)
    | exact resolve eq12475 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12475
  have eq13247 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq12487 eq5622
    | exact resolve eq5622 eq12487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12487
  have eq13253 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13247
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq13247
    | exact resolve eq13247 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13247
  have eq13393 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13253 eq12423
    | exact resolve eq12423 eq13253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12423 eq13253
  have eq13425 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13393
  have eq13450 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13425 eq26
    | exact resolve eq26 eq13425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13454 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13425 eq39
    | exact resolve eq39 eq13425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13425
  have eq13511 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq38 eq13454
    | exact resolve eq13454 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13454
  have eq13520 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq13511 eq39
    | exact resolve eq39 eq13511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13511
  have eq13567 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq37 eq13520
    | exact resolve eq13520 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13520
  have eq13575 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13567 eq38
    | exact resolve eq38 eq13567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13567
  have eq13623 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq37 eq13575
    | exact resolve eq13575 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13575
  have eq14359 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13450 eq12467
    | exact resolve eq12467 eq13450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12467 eq13450
  have eq14392 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14359
  have eq14404 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq14392
       have r₂ := eq27
       grind)
    | exact resolve eq14392 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14392
  have eq14412 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14404 eq39
    | exact resolve eq39 eq14404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq14404
  have eq14459 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq14412
    | exact resolve eq14412 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14412
  have eq14467 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14459 eq38
    | exact resolve eq38 eq14459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14459
  have eq14515 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq14467
    | exact resolve eq14467 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14467
  have eq14519 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14515 eq20
    | exact resolve eq20 eq14515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14520 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14515 eq77
    | exact resolve eq77 eq14515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq14546 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq14515
  have eq14547 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14519
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14519
    | exact resolve eq14519 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14519
  have eq15458 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14520 (M.op y x)
       have i₂ := eq14520 x
       grind)
    | exact superpose eq14520 eq14520
    | exact resolve eq14520 eq14520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14520
  have eq15471 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq15458
  have eq15494 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138 y
       have i₂ := eq15471
       grind)
    | exact superpose eq15471 eq138
    | exact resolve eq138 eq15471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15471
  have eq15524 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15494
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15494
    | exact resolve eq15494 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15494
  have eq15527 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14547 eq15524
    | exact resolve eq15524 eq14547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15524
  have eq15587 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq15527
  have eq15640 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15587 eq5646
    | exact resolve eq5646 eq15587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5646 eq15587
  have eq15697 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq15640
    | exact resolve eq15640 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq15640
  have eq17781 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq13623 eq15697
    | exact resolve eq15697 eq13623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13623 eq15697
  have eq17825 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq17781
  have eq17858 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17825
       have r₂ := eq14546
       grind)
    | exact resolve eq17825 eq14546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14546 eq17825
  have eq17860 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17858
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq17858
    | exact resolve eq17858 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17858
  have eq17862 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17860
       have i₂ := eq138 y
       grind)
    | exact superpose eq138 eq17860
    | exact resolve eq17860 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17860
  have eq17864 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17862
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17862
    | exact resolve eq17862 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17862
  have eq17908 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17864 eq5622
    | exact resolve eq5622 eq17864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17864
  have eq17918 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17908
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq17908
    | exact resolve eq17908 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17908
  have eq17970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17918 eq11221
    | exact resolve eq11221 eq17918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11221 eq17918
  have eq18015 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq17970
    | exact resolve eq17970 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17970
  have eq18027 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18015
       have r₂ := eq27
       grind)
    | exact resolve eq18015 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18015
  have eq18215 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18027 eq14547
    | exact resolve eq14547 eq18027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14547 eq18027
  have eq18222 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq18215
  have eq18239 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18222 eq38
    | exact resolve eq38 eq18222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq18222
  have eq18291 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq18239
    | exact resolve eq18239 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq18239
  have eq18292 : x = (M.op x y) := by grind
  clear eq18291
  have eq18297 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18292 eq20
    | exact resolve eq20 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq18306 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq18292 eq80
    | exact resolve eq80 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq18309 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq18292 eq95
    | exact resolve eq95 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq20026 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq18292 eq18309
    | exact resolve eq18309 eq18292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18292 eq18309
  have eq20029 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18297
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18297
    | exact resolve eq18297 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18297
  have eq20121 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq20029 eq22
    | exact resolve eq22 eq20029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq20122 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20029 eq26
    | exact resolve eq26 eq20029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq20130 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq20029 eq104
    | exact resolve eq104 eq20029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq20029
  have eq21465 : x = (M.op x x) := by
    first
    | (have i₁ := eq18306 (M.op x x)
       have i₂ := eq18306 x
       grind)
    | exact superpose eq18306 eq18306
    | exact resolve eq18306 eq18306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18306
  have eq21573 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq20026
       have i₂ := eq21465
       grind)
    | exact superpose eq21465 eq20026
    | (have r₁ := eq20026
       have r₂ := eq21465
       grind)
    | exact resolve eq20026 eq21465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20026
  have eq21584 : x = (k y x) := by grind
  clear eq21573
  have eq21598 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq20130
       have i₂ := eq21584
       grind)
    | exact superpose eq21584 eq20130
    | exact resolve eq20130 eq21584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20130
  have eq21615 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq21598
       have i₂ := eq20121
       grind)
    | exact superpose eq20121 eq21598
    | exact resolve eq21598 eq20121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21598
  have eq21631 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq21615
       have r₂ := eq27
       grind)
    | exact resolve eq21615 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21615
  have eq21638 : (σ (k y x)) = (σ (k y y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq386 y x
       have i₂ := eq21584
       grind)
    | exact superpose eq21584 eq386
    | (have j0 := eq386 x y
       grind)
    | exact resolve eq386 eq21584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq21648 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21638
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq21638
    | exact resolve eq21638 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21638
  have eq21655 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21648
       have i₂ := eq138 y
       grind)
    | exact superpose eq138 eq21648
    | exact resolve eq21648 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21648
  have eq21661 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21655
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21655
    | exact resolve eq21655 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21655
  have eq21666 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21661
       have i₂ := eq21584
       grind)
    | exact superpose eq21584 eq21661
    | exact resolve eq21661 eq21584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21584 eq21661
  have eq21671 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21666
       have i₂ := eq20121
       grind)
    | exact superpose eq20121 eq21666
    | exact resolve eq21666 eq20121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21666
  have eq21675 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21671
       have i₂ := eq20121
       grind)
    | exact superpose eq20121 eq21671
    | exact resolve eq21671 eq20121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21671
  have eq21678 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21675
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21675
    | exact resolve eq21675 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21675
  have eq21679 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21678
       have i₂ := eq20121
       grind)
    | exact superpose eq20121 eq21678
    | exact resolve eq21678 eq20121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21678
  have eq21680 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq21679
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq21679
    | exact resolve eq21679 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq21679
  have eq21681 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20122 eq21680
    | exact resolve eq21680 eq20122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21680
  have eq21682 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq21681
       have r₂ := eq21631
       grind)
    | exact resolve eq21681 eq21631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21631 eq21681
  have eq21706 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq138 x
       have i₂ := eq21465
       grind)
    | exact superpose eq21465 eq138
    | exact resolve eq138 eq21465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq21465
  have eq21771 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq21706
       have i₂ := eq20121
       grind)
    | exact superpose eq20121 eq21706
    | exact resolve eq21706 eq20121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20121 eq21706
  have eq21953 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21771 eq21682
    | exact resolve eq21682 eq21771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21682
  have eq21956 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by grind
  clear eq21953
  have eq22474 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21956 eq5622
    | exact resolve eq5622 eq21956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5622 eq21956
  have eq22481 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq22474
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq22474
    | exact resolve eq22474 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq22474
  have eq22537 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21771 eq22481
    | exact resolve eq22481 eq21771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22481
  have eq23037 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22537 eq20122
    | exact resolve eq20122 eq22537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20122 eq22537
  have eq23343 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21771 eq23037
    | exact resolve eq23037 eq21771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21771 eq23037
  have eq23396 : False := by grind
  exact eq23396

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pyx_pyy_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y) X0
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
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
  have eq42 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq29 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29
    | (have j0 := eq29 y
       grind)
    | exact resolve eq29 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq81 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
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
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq97 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq59 eq97
    | exact resolve eq97 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq141 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq141 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq141
    | exact resolve eq141 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq173 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq15
    | exact resolve eq15 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq191 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq213 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191
    | (have j0 := eq191 X0 X1
       grind)
    | exact resolve eq191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq220 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq28
    | exact resolve eq28 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq225 : ∀ X0 : G, (σ (k y (M.op X0 X0))) = (k (σ y) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq142 X0
       grind)
    | exact superpose eq142 eq36
    | exact resolve eq36 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1339 : (σ (k (M.op x y) (M.op x x))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq220 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq220
    | (have j0 := eq220 x
       grind)
    | exact resolve eq220 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq2024 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq225
    | (have j0 := eq225 (M.op x y)
       grind)
    | exact resolve eq225 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq2471 : ∀ X0 X1 : G, (σ (k X0 (k (M.op x y) (τ X1)))) = (k (σ X0) (k (σ (M.op x y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq20 eq173
    | (have j0 := eq173 (M.op x y) X1 X0
       grind)
    | exact resolve eq173 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq3713 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (τ (σ (M.op x y)))))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq2471 X0 sF1
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq2471
    | exact resolve eq2471 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq3831 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq37 eq3713
    | exact resolve eq3713 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3713
  have eq3871 : ∀ X0 : G, (k (σ X0) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k X0 (M.op (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq3831 X0
       have i₂ := eq100 sF0
       grind)
    | exact superpose eq100 eq3831
    | exact resolve eq3831 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831
  have eq5556 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq83 eq99
    | (have r₁ := eq99 (M.op x y) y
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq5557 : x ≠ x ∨ x = (k (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq80 eq99
    | (have r₁ := eq99 x (M.op x y)
       have r₂ := eq80 x
       grind)
    | exact resolve eq99 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq5563 : x = (k (M.op x y) (M.op x x)) := by grind
  clear eq5557
  have eq5564 : (M.op x y) = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq5556
  have eq5569 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5563 eq1339
    | exact resolve eq1339 eq5563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339 eq5563
  have eq5572 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq5564 eq2024
    | exact resolve eq2024 eq5564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024 eq5564
  have eq5573 : (σ x) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5569
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5569
    | exact resolve eq5569 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5569
  have eq5576 : (σ (M.op x y)) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq5572
    | exact resolve eq5572 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5572
  have eq6028 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (τ X1)) (M.op X0 X2)) = X0 ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (τ X1) X0 X2
       have i₂ := eq213 X1 X0
       grind)
    | (have i₁ := eq53 X1 (τ X0) x
       have i₂ := eq213 X0 X1
       grind)
    | exact superpose eq213 eq53
    | (have j1 := eq213 X1 X0
       grind)
    | exact resolve eq53 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6036 : ∀ X0 : G, x = (M.op (M.op x (τ X0)) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (M.op x x) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq80 (τ X0)
       have i₂ := eq213 X0 x
       grind)
    | exact superpose eq213 eq80
    | (have j1 := eq213 X0 x
       grind)
    | exact resolve eq80 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6038 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (τ X0)) (M.op (σ x) (σ y))) ∨ (k X0 (σ (σ x))) = X0 ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq81 (τ X0)
       have i₂ := eq213 X0 sF2
       grind)
    | exact superpose eq213 eq81
    | (have j1 := eq213 X0 (σ x)
       grind)
    | exact resolve eq81 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq213
  have eq6129 : ∀ X0 : G, x = (M.op (M.op x (τ X0)) (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ (M.op x x) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6036 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6036
    | (have j0 := eq6036 X0
       grind)
    | exact resolve eq6036 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6036
  have eq238921 : ∀ X0 : G, (M.op x x) = (M.op x (τ X0)) ∨ (k X0 (σ x)) = X0 ∨ (M.op x x) = (M.op x (τ X0)) := by
    intro X0
    first
    | exact superpose eq6129 eq54
    | (have j1 := eq6129 X0
       grind)
    | exact resolve eq54 eq6129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6129
  have eq238927 : ∀ X0 : G, (M.op x x) = (M.op x (τ X0)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq238921 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238921
  have eq238939 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (k (τ X0) x) = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq12 (τ X0) x
       have i₂ := eq238927 X0
       grind)
    | exact superpose eq238927 eq12
    | (have j0 := eq12 x x
       have j1 := eq238927 X0
       grind)
    | (have r₁ := eq12 (τ X0) x
       have r₂ := eq238927 X0
       grind)
    | exact resolve eq12 eq238927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238927
  have eq238951 : ∀ X0 : G, (k (τ X0) x) = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq238939 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238939
  have eq239075 : ∀ X0 : G, (k X0 x) = (M.op x x) ∨ (σ X0) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq238951 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq238951
    | (have j0 := eq238951 (σ X0)
       grind)
    | exact resolve eq238951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238951
  have eq239160 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30 eq239075
    | (have j0 := eq239075 X0
       grind)
    | exact resolve eq239075 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239075
  have eq240901 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 x)
       have i₂ := eq239160 X0
       grind)
    | exact superpose eq239160 eq10
    | (have j1 := eq239160 X0
       grind)
    | exact resolve eq10 eq239160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240906 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k (k X0 x) x)) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq30 (k X0 x)
       have i₂ := eq239160 X0
       grind)
    | exact superpose eq239160 eq30
    | (have j1 := eq239160 X0
       grind)
    | exact resolve eq30 eq239160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239160
  have eq240954 : ∀ X0 : G, (σ (k X0 x)) = (σ (k (k X0 x) x)) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30 eq240906
    | (have j0 := eq240906 X0
       grind)
    | exact resolve eq240906 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq240906
  have eq240959 : ∀ X0 : G, (k X0 x) = X0 ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq240901 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq240901
    | (have j0 := eq240901 X0
       grind)
    | exact resolve eq240901 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240901
  have eq241127 : ∀ X0 : G, (M.op x x) ≠ X0 ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq240959 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240959
  have eq261163 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) ∨ (k X0 (σ (σ x))) = X0 ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) := by
    intro X0
    first
    | exact superpose eq6038 eq54
    | (have j1 := eq6038 X0
       grind)
    | exact resolve eq54 eq6038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6038
  have eq261168 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (τ X0)) ∨ (k X0 (σ (σ x))) = X0 := by
    intro X0
    first
    | (have j0 := eq261163 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261163
  have eq261183 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (σ X0) = (k (σ X0) (σ (σ x))) := by
    intro X0
    first
    | (have i₁ := eq261168 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq261168
    | (have j0 := eq261168 (σ X0)
       grind)
    | exact resolve eq261168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261168
  have eq261207 : ∀ X0 : G, (σ X0) = (σ (k X0 (σ x))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq261183 X0
       have i₂ := eq15 X0 sF2
       grind)
    | exact superpose eq15 eq261183
    | (have j0 := eq261183 X0
       grind)
    | exact resolve eq261183 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261183
  have eq261384 : ∀ X0 : G, (τ (σ X0)) = (k X0 (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq261207 eq10
    | (have j1 := eq261207 X0
       grind)
    | exact resolve eq10 eq261207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261207
  have eq261425 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq261384 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq261384
    | (have j0 := eq261384 X0
       grind)
    | exact resolve eq261384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261384
  have eq261469 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq261425 eq59
    | (have j1 := eq261425 (σ y)
       grind)
    | exact resolve eq59 eq261425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq261425
  have eq261562 : (σ y) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq261469
    | exact resolve eq261469 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261469
  have eq261610 : (τ (σ y)) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq261562
       grind)
    | exact superpose eq261562 eq10
    | exact resolve eq10 eq261562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq261635 : (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (k (k y x) (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3871 (k y x)
       have i₂ := eq261562
       grind)
    | exact superpose eq261562 eq3871
    | exact resolve eq3871 eq261562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3871 eq261562
  have eq261646 : (σ (M.op x y)) = (σ (k (k y x) (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5576 eq261635
    | exact resolve eq261635 eq5576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261635
  have eq261667 : y = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq39 eq261610
    | exact resolve eq261610 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261610
  have eq262565 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (k y x) (M.op (M.op x y) (M.op x y))) (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq261646 eq29
    | exact resolve eq29 eq261646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq261646
  have eq262577 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (k y x) (M.op (M.op x y) (M.op x y))) (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq262565
       have i₂ := eq100 sF1
       grind)
    | exact superpose eq100 eq262565
    | exact resolve eq262565 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262565
  have eq427386 : ∀ X0 : G, (τ (σ (k X0 x))) = (k (k X0 x) x) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 x) x)
       have i₂ := eq240954 X0
       grind)
    | exact superpose eq240954 eq10
    | (have j1 := eq240954 X0
       grind)
    | exact resolve eq10 eq240954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240954
  have eq427399 : ∀ X0 : G, (k X0 x) = (k (k X0 x) x) ∨ (k X0 x) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq427386 X0
       have i₂ := eq10 (k X0 x)
       grind)
    | exact superpose eq10 eq427386
    | (have j0 := eq427386 X0
       grind)
    | exact resolve eq427386 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427386
  have eq427406 : ∀ X0 : G, (k X0 x) = (k (k X0 x) x) := by
    intro X0
    first
    | (have j0 := eq427399 X0
       have j1 := eq241127 (k X0 x)
       grind)
    | (have r₁ := eq427399 X0
       have r₂ := eq241127 (k X0 x)
       grind)
    | exact resolve eq427399 eq241127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241127 eq427399
  have eq449778 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (τ X1) (M.op X0 x)
       have i₂ := eq6028 X0 X1 x
       grind)
    | exact superpose eq6028 eq54
    | (have j1 := eq6028 X0 X1 x
       grind)
    | exact resolve eq54 eq6028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq6028
  have eq450448 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq449778 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449778
  have eq450583 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X1) = (M.op X1 (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq450448 X1 (σ X0)
       grind)
    | exact superpose eq450448 eq15
    | (have j1 := eq450448 X1 (σ X0)
       grind)
    | exact resolve eq15 eq450448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450448
  have eq450628 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq450583 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq450583
    | (have j0 := eq450583 X0 X1
       grind)
    | exact resolve eq450583 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450583
  have eq462183 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq450628 X0 X1
       grind)
    | exact superpose eq450628 eq10
    | (have j1 := eq450628 X0 X1
       grind)
    | exact resolve eq10 eq450628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450628
  have eq462242 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq462183 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq462183
    | (have j0 := eq462183 X0 X1
       grind)
    | exact resolve eq462183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462183
  have eq462476 : (σ (M.op x y)) = (σ x) ∨ (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq5573
       have i₂ := eq462242 sF1 (M.op sF2 sF2)
       grind)
    | exact superpose eq462242 eq5573
    | (have j1 := eq462242 (σ (M.op x y)) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq5573 eq462242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5573
  have eq462480 : (σ (M.op x y)) = (σ y) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq5576
       have i₂ := eq462242 sF3 (M.op sF1 sF1)
       grind)
    | exact superpose eq462242 eq5576
    | (have j1 := eq462242 (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq5576 eq462242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462242
  have eq463244 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq462480
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq462480
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq462480
    | exact resolve eq462480 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462480
  have eq463248 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq462476
       have i₂ := eq53 sF2 sF2 sF2
       grind)
    | (have i₁ := eq462476
       have i₂ := eq53 x (M.op (M.op sF2 sF2) (M.op sF2 sF2)) x
       grind)
    | exact superpose eq53 eq462476
    | exact resolve eq462476 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq462476
  have eq463360 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq463244 eq82
    | exact resolve eq82 eq463244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463244
  have eq463449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq463248 eq463360
    | exact resolve eq463360 eq463248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463360
  have eq463471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq463449
    | exact resolve eq463449 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463449
  have eq463475 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq463471
       have r₂ := eq27
       grind)
    | exact resolve eq463471 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463471
  have eq463480 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq463475 eq39
    | exact resolve eq39 eq463475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq463475
  have eq463806 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq463480
    | exact resolve eq463480 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463480
  have eq463814 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq463806 eq38
    | exact resolve eq38 eq463806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463820 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq463806 eq104
    | exact resolve eq104 eq463806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463806
  have eq464430 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq463814
    | exact resolve eq463814 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463814
  have eq464434 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq464430 eq20
    | exact resolve eq20 eq464430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464435 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq464430 eq77
    | exact resolve eq77 eq464430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq465171 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq465194 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq464434
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq464434
    | exact resolve eq464434 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464434
  have eq470432 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq464435 (M.op y x)
       have i₂ := eq464435 x
       grind)
    | exact superpose eq464435 eq464435
    | exact resolve eq464435 eq464435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464435
  have eq470467 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq470432
  have eq470516 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142 y
       have i₂ := eq470467
       grind)
    | exact superpose eq470467 eq142
    | exact resolve eq142 eq470467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470467
  have eq470649 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq470516
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq470516
    | exact resolve eq470516 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470516
  have eq470710 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq465194 eq470649
    | exact resolve eq470649 eq465194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465194 eq470649
  have eq470829 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq470710
  have eq470987 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq470829 eq5576
    | exact resolve eq5576 eq470829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5576 eq470829
  have eq471166 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42 eq470987
    | exact resolve eq470987 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq470987
  have eq471623 : (σ (M.op x y)) = (σ (k y y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq464430 eq471166
    | exact resolve eq471166 eq464430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464430 eq471166
  have eq472125 : (σ (M.op x y)) = (σ (k y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq471623
       have r₂ := eq465171
       grind)
    | exact resolve eq471623 eq465171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465171 eq471623
  have eq472143 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq472125
       have i₂ := eq100 y
       grind)
    | exact superpose eq100 eq472125
    | exact resolve eq472125 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq472125
  have eq472147 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq472143
       have i₂ := eq142 y
       grind)
    | exact superpose eq142 eq472143
    | exact resolve eq472143 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq472143
  have eq472150 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq472147
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq472147
    | exact resolve eq472147 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472147
  have eq472257 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq472150 eq82
    | exact resolve eq82 eq472150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq472150
  have eq496693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq463248 eq472257
    | exact resolve eq472257 eq463248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463248 eq472257
  have eq496753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq496693
    | exact resolve eq496693 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496693
  have eq496757 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq496753
       have r₂ := eq27
       grind)
    | exact resolve eq496753 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496753
  have eq496762 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq496757 eq38
    | exact resolve eq38 eq496757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq496757
  have eq497385 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq496762
    | exact resolve eq496762 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq496762
  have eq497386 : x = (M.op x y) := by grind
  clear eq497385
  have eq497391 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq497386 eq20
    | exact resolve eq20 eq497386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq497400 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq497386 eq80
    | exact resolve eq80 eq497386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq497403 : x ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | exact superpose eq497386 eq95
    | exact resolve eq95 eq497386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq517032 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (k y x) (M.op x x)) x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq497386 eq262577
    | exact resolve eq262577 eq497386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262577
  have eq520066 : x = y ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq497386 eq463820
    | exact resolve eq463820 eq497386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463820
  have eq523339 : x = (k y x) ∨ x ≠ (M.op x x) := by
    first
    | exact superpose eq497386 eq497403
    | exact resolve eq497403 eq497386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497386 eq497403
  have eq523342 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq497391
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq497391
    | exact resolve eq497391 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497391
  have eq524423 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq523342 eq22
    | exact resolve eq22 eq523342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq524424 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq523342 eq26
    | exact resolve eq26 eq523342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq524432 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq523342 eq104
    | exact resolve eq104 eq523342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq531183 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k y x) := by
    first
    | exact superpose eq523342 eq261667
    | exact resolve eq261667 eq523342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261667
  have eq534251 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (k y x) (M.op x x)) x)) := by
    first
    | exact superpose eq523342 eq517032
    | exact resolve eq517032 eq523342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517032 eq523342
  have eq541121 : x = (M.op x x) := by
    first
    | (have i₁ := eq497400 (M.op x x)
       have i₂ := eq497400 x
       grind)
    | exact superpose eq497400 eq497400
    | exact resolve eq497400 eq497400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497400
  have eq543042 : x ≠ x ∨ x = (k y x) := by
    first
    | (have i₁ := eq523339
       have i₂ := eq541121
       grind)
    | exact superpose eq541121 eq523339
    | (have r₁ := eq523339
       have r₂ := eq541121
       grind)
    | exact resolve eq523339 eq541121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523339
  have eq543241 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k (k y x) x) x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq534251
       have i₂ := eq541121
       grind)
    | exact superpose eq541121 eq534251
    | exact resolve eq534251 eq541121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534251 eq541121
  have eq543540 : x = (k y x) := by grind
  clear eq543042
  have eq543570 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (k y x) x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq543241
       have i₂ := eq427406 (k y x)
       grind)
    | exact superpose eq427406 eq543241
    | exact resolve eq543241 eq427406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543241
  have eq543662 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq520066
       have i₂ := eq543540
       grind)
    | exact superpose eq543540 eq520066
    | exact resolve eq520066 eq543540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520066
  have eq543702 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq524432
       have i₂ := eq543540
       grind)
    | exact superpose eq543540 eq524432
    | exact resolve eq524432 eq543540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524432
  have eq543722 : x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq531183
       have i₂ := eq543540
       grind)
    | exact superpose eq543540 eq531183
    | exact resolve eq531183 eq543540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531183
  have eq544144 : (σ (k y x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq543570
       have i₂ := eq427406 y
       grind)
    | exact superpose eq427406 eq543570
    | exact resolve eq543570 eq427406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427406 eq543570
  have eq544294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq543702
       have i₂ := eq524423
       grind)
    | exact superpose eq524423 eq543702
    | exact resolve eq543702 eq524423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543702
  have eq544322 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq543662
       have r₂ := eq543722
       grind)
    | exact resolve eq543662 eq543722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543662 eq543722
  have eq544433 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq544144
       have i₂ := eq543540
       grind)
    | exact superpose eq543540 eq544144
    | exact resolve eq544144 eq543540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543540 eq544144
  have eq544475 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq544294
       have r₂ := eq27
       grind)
    | exact resolve eq544294 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544294
  have eq544482 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq544322
       have i₂ := eq524423
       grind)
    | exact superpose eq524423 eq544322
    | exact resolve eq544322 eq524423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544322
  have eq544510 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq544433
       have i₂ := eq524423
       grind)
    | exact superpose eq524423 eq544433
    | exact resolve eq544433 eq524423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544433
  have eq544546 : x = y := by
    first
    | (have r₁ := eq544482
       have r₂ := eq27
       grind)
    | exact resolve eq544482 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544482
  have eq544562 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq544510
       have r₂ := eq544475
       grind)
    | exact resolve eq544510 eq544475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544475 eq544510
  have eq544581 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq544546
       grind)
    | exact superpose eq544546 eq24
    | exact resolve eq24 eq544546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq544546
  have eq557405 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq544581
       have i₂ := eq524423
       grind)
    | exact superpose eq524423 eq544581
    | exact resolve eq544581 eq524423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524423 eq544581
  have eq558031 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq557405 eq524424
    | exact resolve eq524424 eq557405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524424 eq557405
  have eq562763 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq544562 eq558031
    | exact resolve eq558031 eq544562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544562 eq558031
  have eq563517 : False := by grind
  exact eq563517

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_pyx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15
    | (have j0 := eq15 y X0
       grind)
    | exact resolve eq15 eq24
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq59 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq78 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y) X0
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 X0 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq78 eq53
    | exact resolve eq53 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq59 eq97
    | exact resolve eq97 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq139 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq100 (σ X0)
       grind)
    | exact superpose eq100 eq15
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq100 X0
       grind)
    | exact superpose eq100 eq139
    | exact resolve eq139 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq139
  have eq169 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq189 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq211 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = X0 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq189 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq189
    | (have j0 := eq189 X0 X1
       grind)
    | exact resolve eq189 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq215 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq10
    | exact resolve eq10 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq169 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq169
    | exact resolve eq169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq261 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq215 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215
    | exact resolve eq215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq350 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 x) x) X0
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | (have r₁ := eq12 (M.op (M.op x x) x) x
       have r₂ := eq54 x x x
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X0 x) x) X0
       have i₂ := eq54 X0 x x
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq366 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq59 eq366
    | exact resolve eq366 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq366
  have eq376 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq357 X0 X1 X2
       have j1 := eq350 X0 X1 X2
       grind)
    | (have r₁ := eq357 X0 X1 X2
       have r₂ := eq350 X0 X1 X2
       grind)
    | (have r₁ := eq357 X1 X1 X2
       have r₂ := eq350 X1 X1 X2
       grind)
    | exact resolve eq357 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq377 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq371
       have r₂ := eq104
       grind)
    | exact resolve eq371 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq7686 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq85 eq99
    | (have r₁ := eq99 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq85 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq99 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq7687 : (σ x) ≠ (σ x) ∨ (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq81 eq99
    | (have r₁ := eq99 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq81 (σ x)
       grind)
    | exact resolve eq99 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq99
  have eq7689 : (σ x) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by grind
  clear eq7687
  have eq7690 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by grind
  clear eq7686
  have eq7710 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq7689 eq227
    | exact resolve eq227 eq7689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7713 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) (M.op (τ (σ x)) (τ (σ x)))) := by
    first
    | (have i₁ := eq7710
       have i₂ := eq261 sF2
       grind)
    | exact superpose eq261 eq7710
    | exact resolve eq7710 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7710
  have eq7718 : x = (k (τ (M.op (σ x) (σ y))) (M.op x x)) := by
    first
    | exact superpose eq38 eq7713
    | exact resolve eq7713 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7713
  have eq7749 : (τ (M.op (σ x) (σ y))) = (k (τ (σ y)) (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq7690 eq227
    | exact resolve eq227 eq7690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq7690
  have eq7752 : (τ (M.op (σ x) (σ y))) = (k (τ (σ y)) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq7749
       have i₂ := eq261 sF4
       grind)
    | exact superpose eq261 eq7749
    | exact resolve eq7749 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7749
  have eq7758 : (τ (M.op (σ x) (σ y))) = (k y (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq39 eq7752
    | exact resolve eq7752 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7752
  have eq8180 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) ≠ (M.op X0 (τ X1)) ∨ (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq350 X1 X1 X2
       have i₂ := eq211 X0 X1
       grind)
    | (have i₁ := eq350 X1 (τ X0) X2
       have i₂ := eq211 X0 X1
       grind)
    | exact superpose eq211 eq350
    | (have j0 := eq350 X0 (τ X1) X2
       have j1 := eq211 X1 X0
       grind)
    | (have r₁ := eq350 X1 (τ X0) X2
       have r₂ := eq211 X0 X1
       grind)
    | (have r₁ := eq350 (τ X0) (τ X0) X2
       have r₂ := eq211 X0 (τ X0)
       grind)
    | exact resolve eq350 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq350
  have eq8266 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq8180 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8180
  have eq8315 : ∀ X0 X1 X2 : G, (M.op X0 (τ X1)) = (k (M.op (M.op X0 (τ X1)) X2) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq8266 X0 X1 X2
       have j1 := eq376 X0 (τ X1) X2
       grind)
    | (have r₁ := eq8266 X0 X1 X2
       have r₂ := eq376 X0 (τ X1) X2
       grind)
    | exact resolve eq8266 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq8266
  have eq130264 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8315 X1 X0 (M.op (τ X0) x)
       have i₂ := eq53 X1 (τ X0) x
       grind)
    | exact superpose eq53 eq8315
    | (have j0 := eq8315 X1 X0 x
       grind)
    | exact resolve eq8315 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8315
  have eq130274 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (σ y) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | exact superpose eq39 eq130264
    | (have j0 := eq130264 (σ y) X0
       grind)
    | exact resolve eq130264 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130290 : x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ (M.op x x))) := by
    first
    | (have i₁ := eq7718
       have i₂ := eq130264 sF4 (M.op x x)
       grind)
    | exact superpose eq130264 eq7718
    | (have j1 := eq130264 (M.op (σ x) (σ y)) (M.op x x)
       grind)
    | exact resolve eq7718 eq130264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7718 eq130264
  have eq130352 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq130290
       have i₂ := eq140 x
       grind)
    | exact superpose eq140 eq130290
    | exact resolve eq130290 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq130290
  have eq130362 : ∀ X0 : G, (σ y) = (σ (k y X0)) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq36 eq130274
    | (have j0 := eq130274 X0
       grind)
    | exact resolve eq130274 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq130274
  have eq130387 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq130352
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq130352
    | exact resolve eq130352 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130352
  have eq130399 : x = (M.op (M.op x x) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7689 eq130387
    | exact resolve eq130387 eq7689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7689 eq130387
  have eq130414 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op x (M.op (τ (M.op (σ x) (σ y))) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130399 eq53
    | exact resolve eq53 eq130399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130399
  have eq130495 : (σ y) = (σ (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) y) := by
    first
    | exact superpose eq7758 eq130362
    | exact resolve eq130362 eq7758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7758
  have eq130667 : ∀ X0 : G, (k y X0) = (τ (σ y)) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq10 (k y X0)
       have i₂ := eq130362 X0
       grind)
    | exact superpose eq130362 eq10
    | (have j1 := eq130362 X0
       grind)
    | exact resolve eq10 eq130362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130362
  have eq130751 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = (k y X0) := by
    intro X0
    first
    | exact superpose eq39 eq130667
    | (have j0 := eq130667 X0
       grind)
    | exact resolve eq130667 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130667
  have eq130895 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq130495
       have i₂ := eq11 sF4
       grind)
    | exact superpose eq11 eq130495
    | exact resolve eq130495 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130495
  have eq131089 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq130751 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131216 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq131089 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq131089
    | (have j0 := eq131089 x
       grind)
    | exact resolve eq131089 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131089
  have eq132633 : ∀ X0 : G, y = (M.op (τ (M.op (σ x) (σ y))) (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq130895 eq53
    | exact resolve eq53 eq130895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq130895
  have eq132655 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq132633 eq130414
    | exact resolve eq130414 eq132633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132633
  have eq132671 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq132655
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq132655
    | exact resolve eq132655 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132655
  have eq132683 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq132671 eq11
    | exact resolve eq11 eq132671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132671
  have eq132984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq132683
    | exact resolve eq132683 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132683
  have eq132986 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq132984
       have r₂ := eq27
       grind)
    | exact resolve eq132984 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132984
  have eq132988 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq132986 eq78
    | exact resolve eq78 eq132986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq133005 : ∀ X0 : G, (τ (σ y)) = (M.op x (M.op (τ (σ y)) X0)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq132986 eq130414
    | exact resolve eq130414 eq132986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130414
  have eq133007 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq133010 : ∀ X0 : G, (τ (σ y)) = (M.op x (M.op (τ (σ y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq133005 X0
       grind)
    | (have r₁ := eq133005 X0
       have r₂ := eq133007
       grind)
    | exact resolve eq133005 eq133007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133005 eq133007
  have eq133021 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq39 eq133010
    | exact resolve eq133010 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133010
  have eq133023 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq132988 eq132988
    | exact resolve eq132988 eq132988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132988
  have eq133047 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq133023
  have eq133106 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq133047 eq261
    | exact resolve eq261 eq133047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261 eq133047
  have eq133168 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq39 eq133106
    | exact resolve eq133106 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq133106
  have eq133773 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq133021 y
       have i₂ := eq133168
       grind)
    | exact superpose eq133168 eq133021
    | exact resolve eq133021 eq133168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133021 eq133168
  have eq133791 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq133773
  have eq133792 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq133791
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq133791
    | exact resolve eq133791 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133791
  have eq133794 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133792 eq27
    | exact resolve eq27 eq133792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133802 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133792 eq377
    | (have r₁ := eq377
       have r₂ := eq133792
       grind)
    | exact resolve eq377 eq133792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133792
  have eq133813 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq133802
  have eq133827 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq133813
       have i₂ := eq130751 x
       grind)
    | exact superpose eq130751 eq133813
    | (have j1 := eq130751 x
       grind)
    | exact resolve eq133813 eq130751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133848 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq133813
       grind)
    | exact superpose eq133813 eq10
    | exact resolve eq10 eq133813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133992 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq133848
    | exact resolve eq133848 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq133848
  have eq134010 : (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by
    first
    | (have r₁ := eq133827
       have r₂ := eq131216
       grind)
    | exact resolve eq133827 eq131216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133827
  have eq134031 : (σ (M.op x y)) = (σ x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq134010
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq134010
    | exact resolve eq134010 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134010
  have eq134043 : y = (k y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq134031
    | exact resolve eq134031 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134031
  have eq134194 : (σ y) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq133813
       have i₂ := eq134043
       grind)
    | exact superpose eq134043 eq133813
    | exact resolve eq133813 eq134043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133813
  have eq134195 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq133992
       have i₂ := eq134043
       grind)
    | exact superpose eq134043 eq133992
    | exact resolve eq133992 eq134043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133992 eq134043
  have eq134205 : y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq134195
       have r₂ := eq133794
       grind)
    | exact resolve eq134195 eq133794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134195
  have eq134206 : (σ y) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq134194
       have r₂ := eq133794
       grind)
    | exact resolve eq134194 eq133794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133794 eq134194
  have eq134212 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq134206
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq134206
    | exact resolve eq134206 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134206
  have eq134215 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq134205 eq20
    | exact resolve eq20 eq134205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134205
  have eq134426 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq134215
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq134215
    | exact resolve eq134215 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134215
  have eq134431 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134212 eq26
    | exact resolve eq26 eq134212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq134212
  have eq135063 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134431 eq104
    | (have r₁ := eq104
       have r₂ := eq134431
       grind)
    | exact resolve eq104 eq134431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq134431
  have eq135133 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq135063
  have eq136528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq135133
       have i₂ := eq130751 x
       grind)
    | exact superpose eq130751 eq135133
    | (have j1 := eq130751 x
       grind)
    | exact resolve eq135133 eq130751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130751 eq135133
  have eq136688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have r₁ := eq136528
       have r₂ := eq131216
       grind)
    | exact resolve eq136528 eq131216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131216 eq136528
  have eq136712 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq136688
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq136688
    | exact resolve eq136688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136688
  have eq136724 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
    first
    | exact superpose eq20 eq136712
    | exact resolve eq136712 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136712
  have eq136727 : y = (k y x) := by
    first
    | (have r₁ := eq136724
       have r₂ := eq27
       grind)
    | exact resolve eq136724 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136724
  have eq136730 : y = (M.op x y) ∨ (M.op x y) ≠ (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq136727
       grind)
    | exact superpose eq136727 eq95
    | exact resolve eq95 eq136727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq136734 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq377
       have i₂ := eq136727
       grind)
    | exact superpose eq136727 eq377
    | exact resolve eq377 eq136727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq136727
  have eq137065 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq136734
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq136734
    | exact resolve eq136734 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136734
  have eq137080 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq137065
       have r₂ := eq132986
       grind)
    | exact resolve eq137065 eq132986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132986 eq137065
  have eq137087 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq137080 eq27
    | exact resolve eq27 eq137080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq137080
  have eq138027 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq134426 eq137087
    | (have r₁ := eq137087
       have r₂ := eq134426
       grind)
    | exact resolve eq137087 eq134426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134426
  have eq138029 : x = y := by grind
  clear eq138027
  have eq138030 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq138029
       grind)
    | exact superpose eq138029 eq18
    | exact resolve eq18 eq138029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq138031 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq138029
       grind)
    | exact superpose eq138029 eq24
    | exact resolve eq24 eq138029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq152116 : x = (M.op x y) ∨ (M.op x y) ≠ (M.op x x) := by
    first
    | (have i₁ := eq136730
       have i₂ := eq138029
       grind)
    | exact superpose eq138029 eq136730
    | exact resolve eq136730 eq138029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136730 eq138029
  have eq153285 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq138031
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq138031
    | exact resolve eq138031 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138031
  have eq153664 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq152116
       have i₂ := eq138030
       grind)
    | exact superpose eq138030 eq152116
    | (have r₁ := eq152116
       have r₂ := eq138030
       grind)
    | exact resolve eq152116 eq138030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138030 eq152116
  have eq153682 : x = (M.op x y) := by grind
  clear eq153664
  have eq154165 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq153285 eq137087
    | exact resolve eq137087 eq153285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137087 eq153285
  have eq157813 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq153682 eq20
    | exact resolve eq20 eq153682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq153682
  have eq168357 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq157813
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq157813
    | exact resolve eq157813 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq157813
  have eq169409 : False := by grind
  exact eq169409
