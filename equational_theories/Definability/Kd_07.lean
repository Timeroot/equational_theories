import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3499`: `x ◇ x = y ◇ ((z ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pxy_pyx_Equation3499 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3499 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3499.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op (M.op X2 X2) X0)) := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq29 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X1 X1) X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X1 X1) X0) X2 x
       have i₂ := eq9 X0 (M.op x x) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq29 X0 x X2
       have i₂ := eq9 X0 (M.op (M.op x x) X0) x
       grind)
    | (have i₁ := eq29 X0 x X2
       have i₂ := eq9 (M.op (M.op x x) X0) x X2
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq47 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq51 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq51
  have eq56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq59 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X0 X2
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq31
    | (have j1 := eq14 X0 X2
       grind)
    | exact resolve eq31 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq56
    | (have j0 := eq56 X0 X1
       grind)
    | exact resolve eq56 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (σ X0) x
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq31
    | exact resolve eq31 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X2) (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op X0 (M.op (M.op X1 X1) (τ X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X2
       have i₂ := eq9 (τ X2) X0 X1
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq10
    | exact resolve eq10 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq578 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 (τ X0) x
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq31
    | exact resolve eq31 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : ∀ X0 X1 : G, (τ (τ (M.op X0 X0))) = (M.op X1 (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq578 (τ X0) X1
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq578
    | exact resolve eq578 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1662 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 x y
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 (M.op y y) y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2810 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (σ (M.op X0 (M.op (M.op X1 X1) (τ (σ X2))))) := by
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
  have eq2832 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = (σ (M.op X0 (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2810 X0 X1 X2
       have i₂ := eq10 X2
       grind)
    | exact superpose eq10 eq2810
    | exact resolve eq2810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810
  have eq4330 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (σ (M.op X2 (M.op (τ (M.op X0 X0)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2832 X2 (τ X0) X1
       have i₂ := eq188 X0
       grind)
    | exact superpose eq188 eq2832
    | exact resolve eq2832 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq2832
  have eq5493 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (M.op X2 (M.op (τ (τ (M.op X0 X0))) (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88 X1 X2 (τ (τ (M.op X0 X0)))
       have i₂ := eq928 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq928 eq88
    | exact resolve eq88 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq5505 : ∀ X0 X1 : G, (τ (τ (τ (M.op X0 X0)))) = (M.op X1 (τ (τ (τ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq578 (τ (τ (M.op X0 X0))) X1
       have i₂ := eq928 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq928 eq578
    | exact resolve eq578 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq37684 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1662
       have i₂ := eq59 y X0 x
       grind)
    | exact superpose eq59 eq1662
    | (have j1 := eq59 y X0 (M.op X0 y)
       grind)
    | (have r₁ := eq1662
       have r₂ := eq59 (σ (M.op x y)) x (σ (k y x))
       grind)
    | (have r₁ := eq1662
       have r₂ := eq59 (σ (k y x)) x (σ (M.op x y))
       grind)
    | exact resolve eq1662 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq1662
  have eq37690 : ∀ X0 : G, (σ y) = (σ (M.op y y)) ∨ y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq37684 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37684
  have eq134446 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (M.op X2 (M.op (τ (τ (τ (τ (M.op X0 X0))))) (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5493 (τ (τ (M.op X0 X0))) X1 X2
       have i₂ := eq928 X0 (τ (τ (M.op X0 X0)))
       grind)
    | exact superpose eq928 eq5493
    | exact resolve eq5493 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq5493
  have eq147144 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (σ (M.op X2 (M.op (τ (τ (τ (τ (M.op X0 X0))))) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4330 (τ (τ (τ (M.op X0 X0)))) X1 X2
       have i₂ := eq5505 X0 (τ (τ (τ (M.op X0 X0))))
       grind)
    | exact superpose eq5505 eq4330
    | exact resolve eq4330 eq5505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4330 eq5505
  have eq290335 : ∀ X0 : G, (M.op y y) = (τ (σ y)) ∨ y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq37690 X0
       grind)
    | exact superpose eq37690 eq10
    | (have j1 := eq37690 X0
       grind)
    | exact resolve eq10 eq37690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37690
  have eq290336 : ∀ X0 : G, y = (M.op y y) ∨ y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq290335 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq290335
    | (have j0 := eq290335 y
       grind)
    | exact resolve eq290335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290335
  have eq470481 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq290336 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290336
  have eq470482 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq470481
  have eq470485 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq31 y x
       have i₂ := eq470482
       grind)
    | exact superpose eq470482 eq31
    | exact resolve eq31 eq470482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq470487 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq86 y x
       have i₂ := eq470482
       grind)
    | exact superpose eq470482 eq86
    | exact resolve eq86 eq470482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq470482
  have eq470828 : ∀ X0 : G, (σ (M.op y y)) = (σ (M.op X0 y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq147144 x y X0
       have i₂ := eq470485 (τ (τ (τ (τ (M.op x x)))))
       grind)
    | exact superpose eq470485 eq147144
    | exact resolve eq147144 eq470485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147144 eq470485
  have eq471076 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq134446 x y X0
       have i₂ := eq470487 (τ (τ (τ (τ (M.op x x)))))
       grind)
    | exact superpose eq470487 eq134446
    | exact resolve eq134446 eq470487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134446 eq470487
  have eq476015 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq471076 (σ x)
       grind)
    | exact superpose eq471076 eq16
    | exact resolve eq16 eq471076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471076
  have eq476080 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq476015
       have r₂ := eq470828 x
       grind)
    | exact resolve eq476015 eq470828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470828 eq476015
  have eq476121 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq476080
       grind)
    | exact superpose eq476080 eq10
    | exact resolve eq10 eq476080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476080
  have eq476321 : x = y ∨ x = y := by
    first
    | (have i₁ := eq476121
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq476121
    | exact resolve eq476121 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476121
  have eq476322 : x = y := by grind
  clear eq476321
  have eq476383 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq476322
       grind)
    | exact superpose eq476322 eq16
    | exact resolve eq16 eq476322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476322
  have eq476388 : False := by grind
  exact eq476388

/-- `Equation3529`: `x ◇ y = x ◇ ((z ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation3529 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3529 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3529.models_iff G M).mp hM
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
  have eq47 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq151 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq158 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq618 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47
    | exact resolve eq47 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq650 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq618 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq618
    | (have j0 := eq618 X0 X1
       grind)
    | exact resolve eq618 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq1288 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq151
       have i₂ := eq650 y x
       grind)
    | exact superpose eq650 eq151
    | (have j1 := eq650 (σ y) (σ x)
       grind)
    | (have r₁ := eq151
       have r₂ := eq650 y x
       grind)
    | (have r₁ := eq151
       have r₂ := eq650 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq151
       have r₂ := eq650 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq151 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq1289 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1288
  have eq19781 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1289
       grind)
    | exact superpose eq1289 eq16
    | exact resolve eq16 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19788 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1289
       grind)
    | exact superpose eq1289 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1289
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1289
       grind)
    | exact resolve eq13 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq19834 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19788
  have eq19835 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq19834
  have eq19837 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq19835
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19835
    | exact resolve eq19835 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19835
  have eq20369 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq650 y x
       have i₂ := eq19837
       grind)
    | exact superpose eq19837 eq650
    | (have j0 := eq650 y x
       grind)
    | exact resolve eq650 eq19837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650 eq19837
  have eq20441 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20369
  have eq20481 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20441
       have r₂ := eq19781
       grind)
    | exact resolve eq20441 eq19781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19781 eq20441
  have eq20678 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq20481
       grind)
    | exact superpose eq20481 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq20481
       grind)
    | exact resolve eq13 eq20481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20724 : x ≠ x ∨ x = y ∨ x = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq20678
  have eq20725 : x = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq20724
  have eq21203 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq158 x y
       have i₂ := eq20725
       grind)
    | exact superpose eq20725 eq158
    | (have j0 := eq158 x y
       grind)
    | exact resolve eq158 eq20725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq20725
  have eq21227 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21203
  have eq21228 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21227
  have eq21434 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq21228
       grind)
    | exact superpose eq21228 eq16
    | exact resolve eq16 eq21228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21228
  have eq21688 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq21434
       have i₂ := eq20481
       grind)
    | exact superpose eq20481 eq21434
    | exact resolve eq21434 eq20481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20481 eq21434
  have eq21689 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq21688
  have eq21690 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq21689
  have eq22196 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21690
       grind)
    | exact superpose eq21690 eq10
    | exact resolve eq10 eq21690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21690
  have eq22301 : x = y ∨ x = y := by
    first
    | (have i₁ := eq22196
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22196
    | exact resolve eq22196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22196
  have eq22302 : x = y := by grind
  clear eq22301
  have eq22776 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22302
       grind)
    | exact superpose eq22302 eq16
    | exact resolve eq16 eq22302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22302
  have eq22777 : False := by grind
  exact eq22777

/-- `Equation3534`: `x ◇ y = x ◇ ((z ◇ y) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation3534 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3534 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3534.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq49 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq92 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq590 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq628 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq590
    | (have j0 := eq590 X0 X1
       grind)
    | exact resolve eq590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq1021 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
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
  have eq1022 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1021
  have eq6403 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1022
       grind)
    | exact superpose eq1022 eq16
    | exact resolve eq16 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6407 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1022
       grind)
    | exact superpose eq1022 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1022
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1022
       grind)
    | exact resolve eq13 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq6414 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6407
  have eq6415 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6414
  have eq6417 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6415
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq6415
    | exact resolve eq6415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6415
  have eq10097 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq628 x y
       have i₂ := eq6417
       grind)
    | exact superpose eq6417 eq628
    | (have j0 := eq628 x y
       grind)
    | exact resolve eq628 eq6417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq6417
  have eq10151 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10097
  have eq10179 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq10151
       have r₂ := eq6403
       grind)
    | exact resolve eq10151 eq6403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6403 eq10151
  have eq10364 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq10179
       grind)
    | exact superpose eq10179 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq10179
       grind)
    | exact resolve eq13 eq10179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10371 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq10364
  have eq10372 : y = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq10371
  have eq10564 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96 x y
       have i₂ := eq10372
       grind)
    | exact superpose eq10372 eq96
    | (have j0 := eq96 x y
       grind)
    | exact resolve eq96 eq10372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq10372
  have eq10576 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10564
  have eq10577 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10576
  have eq10775 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq10577
       grind)
    | exact superpose eq10577 eq16
    | exact resolve eq16 eq10577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10577
  have eq10990 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10775
       have i₂ := eq10179
       grind)
    | exact superpose eq10179 eq10775
    | exact resolve eq10775 eq10179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10179 eq10775
  have eq10991 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq10990
  have eq10992 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq10991
  have eq11209 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq10992
       grind)
    | exact superpose eq10992 eq10
    | exact resolve eq10 eq10992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10992
  have eq11286 : x = y ∨ x = y := by
    first
    | (have i₁ := eq11209
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11209
    | exact resolve eq11209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11209
  have eq11287 : x = y := by grind
  clear eq11286
  have eq11450 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11287
       grind)
    | exact superpose eq11287 eq16
    | exact resolve eq16 eq11287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11287
  have eq11451 : False := by grind
  exact eq11451

/-- `Equation3537`: `x ◇ y = x ◇ ((z ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3537 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3537 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3537.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq63 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  have eq92 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    grind
  have eq94 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq92 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq255 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0
       have i₂ := eq58 X0 X1
       grind)
    | (have i₁ := eq94 X0
       have i₂ := eq58 X0 (M.op X0 X0)
       grind)
    | exact superpose eq58 eq94
    | (have j1 := eq58 X1 X0
       grind)
    | exact resolve eq94 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq272 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq255 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq413 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq272 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq414 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq413 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq495 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq414 (σ X0)
       grind)
    | exact superpose eq414 eq15
    | exact resolve eq15 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq495 X0
       have i₂ := eq414 X0
       grind)
    | exact superpose eq414 eq495
    | exact resolve eq495 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq495
  have eq723 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq730 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq502 X0
       grind)
    | exact superpose eq502 eq94
    | exact resolve eq94 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq736 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq730 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq730
    | exact resolve eq730 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq739 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq723 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq723
    | exact resolve eq723 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq742 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq736 X0
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq736
    | exact resolve eq736 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq736
  have eq745 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq739
  have eq1213 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq10
    | (have j1 := eq62 X1 X0
       grind)
    | exact resolve eq10 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq1310 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1213 X0 X1
       have i₂ := eq502 X0
       grind)
    | exact superpose eq502 eq1213
    | (have j0 := eq1213 X0 X1
       grind)
    | exact resolve eq1213 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213
  have eq1418 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1310 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1310
    | (have j0 := eq1310 X0 X1
       grind)
    | exact resolve eq1310 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1468 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1418 X0 X1
       have i₂ := eq502 X1
       grind)
    | exact superpose eq502 eq1418
    | (have j0 := eq1418 X0 X1
       grind)
    | exact resolve eq1418 eq502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq1418
  have eq11165 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1468 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1468 X0 X1
       grind)
    | exact superpose eq1468 eq10
    | (have j1 := eq1468 X0 X1
       grind)
    | exact resolve eq10 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq11501 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11165 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11165
    | (have j0 := eq11165 X0 X1
       grind)
    | exact resolve eq11165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11165
  have eq13692 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq14340 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13692 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13692
    | (have j0 := eq13692 X0 X1
       grind)
    | exact resolve eq13692 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13692
  have eq316812 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11501 y x
       grind)
    | exact superpose eq11501 eq16
    | (have j1 := eq11501 y x
       grind)
    | exact resolve eq16 eq11501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11501
  have eq316886 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq14340 x y
       grind)
    | (have r₁ := eq316812
       have r₂ := eq14340 x y
       grind)
    | exact resolve eq316812 eq14340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14340 eq316812
  have eq319877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq745 y
       have i₂ := eq316886
       grind)
    | exact superpose eq316886 eq745
    | exact resolve eq745 eq316886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq316886
  have eq319992 : y = (M.op x x) := by
    first
    | (have r₁ := eq319877
       have r₂ := eq16
       grind)
    | exact resolve eq319877 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319877
  have eq323261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq742 x
       have i₂ := eq319992
       grind)
    | exact superpose eq319992 eq742
    | exact resolve eq742 eq319992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq319992
  have eq323440 : False := by grind
  exact eq323440

/-- `Equation3545`: `x ◇ y = y ◇ ((x ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation3545 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3545 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3545.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq50 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq51 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq107 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51 x y
       grind)
    | exact superpose eq51 eq16
    | (have j1 := eq51 x y
       grind)
    | exact resolve eq16 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq925 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq50 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq50
    | exact resolve eq50 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq963 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq925 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq925
    | (have j0 := eq925 X0 X1
       grind)
    | exact resolve eq925 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq1357 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq107
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq107
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq107
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq107
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq107 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq1358 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1357
  have eq11518 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1358
       grind)
    | exact superpose eq1358 eq16
    | exact resolve eq16 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11519 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1358
       grind)
    | exact superpose eq1358 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1358
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1358
       grind)
    | exact resolve eq13 eq1358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358
  have eq11520 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq11519
  have eq11521 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq11520
  have eq11523 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11521
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq11521
    | exact resolve eq11521 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11521
  have eq16829 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq963 x y
       have i₂ := eq11523
       grind)
    | exact superpose eq11523 eq963
    | (have j0 := eq963 x y
       grind)
    | exact resolve eq963 eq11523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq16831 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq11523
       grind)
    | exact superpose eq11523 eq10
    | exact resolve eq10 eq11523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11523
  have eq16874 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16829
  have eq16897 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16831
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq16831
    | exact resolve eq16831 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16831
  have eq16898 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16874
       have r₂ := eq11518
       grind)
    | exact resolve eq16874 eq11518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11518 eq16874
  have eq16901 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq16897
       have r₂ := eq13 y x
       grind)
    | exact resolve eq16897 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16897
  have eq17903 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq109 x y
       have i₂ := eq16901
       grind)
    | exact superpose eq16901 eq109
    | (have j0 := eq109 x y
       grind)
    | exact resolve eq109 eq16901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq16901
  have eq17906 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17903
  have eq17907 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17906
  have eq18687 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq17907
       grind)
    | exact superpose eq17907 eq16
    | exact resolve eq16 eq17907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17907
  have eq18864 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18687
       have i₂ := eq16898
       grind)
    | exact superpose eq16898 eq18687
    | exact resolve eq18687 eq16898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16898 eq18687
  have eq18865 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18864
  have eq18866 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq18865
  have eq19041 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18866
       grind)
    | exact superpose eq18866 eq10
    | exact resolve eq10 eq18866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18866
  have eq19108 : x = y ∨ x = y := by
    first
    | (have i₁ := eq19041
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq19041
    | exact resolve eq19041 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19041
  have eq19109 : x = y := by grind
  clear eq19108
  have eq19240 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19109
       grind)
    | exact superpose eq19109 eq16
    | exact resolve eq16 eq19109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19109
  have eq19241 : False := by grind
  exact eq19241

/-- `Equation3558`: `x ◇ y = y ◇ ((y ◇ y) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation3558 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3558 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3558.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  have eq45 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq46 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq80 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
  have eq82 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq301 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq331 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq301 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq301
    | (have j0 := eq301 X0 X1
       grind)
    | exact resolve eq301 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq700 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq80
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq80
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq80
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq80
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq80 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq701 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq700
  have eq4011 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq701
       grind)
    | exact superpose eq701 eq16
    | exact resolve eq16 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4012 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq701
       grind)
    | exact superpose eq701 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq701
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq701
       grind)
    | exact resolve eq13 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq4013 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4012
  have eq4014 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq4013
  have eq4016 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4014
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4014
    | exact resolve eq4014 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014
  have eq7287 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq331 x y
       have i₂ := eq4016
       grind)
    | exact superpose eq4016 eq331
    | (have j0 := eq331 x y
       grind)
    | exact resolve eq331 eq4016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq7289 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq4016
       grind)
    | exact superpose eq4016 eq10
    | exact resolve eq10 eq4016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4016
  have eq7334 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq7287
  have eq7365 : y = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq7289
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq7289
    | exact resolve eq7289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7289
  have eq7366 : y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq7334
       have r₂ := eq4011
       grind)
    | exact resolve eq7334 eq4011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4011 eq7334
  have eq7369 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 y (k y x)
       grind)
    | (have r₁ := eq7365
       have r₂ := eq13 y x
       grind)
    | exact resolve eq7365 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7365
  have eq7726 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq82 x y
       have i₂ := eq7369
       grind)
    | exact superpose eq7369 eq82
    | (have j0 := eq82 x y
       grind)
    | exact resolve eq82 eq7369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq7369
  have eq7729 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7726
  have eq7730 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq7729
  have eq7945 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq7730
       grind)
    | exact superpose eq7730 eq16
    | exact resolve eq16 eq7730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7730
  have eq8122 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq7945
       have i₂ := eq7366
       grind)
    | exact superpose eq7366 eq7945
    | exact resolve eq7945 eq7366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7366 eq7945
  have eq8123 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq8122
  have eq8124 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq8123
  have eq8296 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8124
       grind)
    | exact superpose eq8124 eq10
    | exact resolve eq10 eq8124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8124
  have eq8378 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8296
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8296
    | exact resolve eq8296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8296
  have eq8379 : x = y := by grind
  clear eq8378
  have eq8513 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8379
       grind)
    | exact superpose eq8379 eq16
    | exact resolve eq16 eq8379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8379
  have eq8514 : False := by grind
  exact eq8514

/-- `Equation3566`: `x ◇ y = y ◇ ((z ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_y_pxx_Equation3566 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) Law3566 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3566.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op (M.op X2 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X3 (M.op (M.op X0 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X1) X3 X1
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X0 X1 X2 X3
       have i₂ := eq9 X1 X3 X0
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq29 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
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
  have eq69 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X2) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
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
  have eq71 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq88 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq25 X0 X1 (M.op x x) X4
       have i₂ := eq25 x X0 x X1
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) ≠ (M.op X0 (M.op (M.op X1 X2) X0)) ∨ (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 (M.op (M.op X1 X2) X0)
       have i₂ := eq25 X2 X0 X1 (M.op (M.op X1 X2) X0)
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 X3 (M.op (M.op X1 X2) X0)
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) ≠ (M.op (M.op X1 X2) X0) ∨ (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq100 X0 X1 X2 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq100
    | (have j0 := eq100 X0 X1 X2 X3
       grind)
    | exact resolve eq100 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq107 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X1 X2) X0)) = (M.op (M.op (M.op X1 X2) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq101 X0 X1 X2 X3
       grind)
    | (have r₁ := eq101 x X0 X1 X3
       have r₂ := eq88 X0 X1 x
       grind)
    | exact resolve eq101 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq110 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k X3 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq107 X0 X1 X2 X3
       have i₂ := eq25 X2 X0 X1 X3
       grind)
    | exact superpose eq25 eq107
    | exact resolve eq107 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq107
  have eq113 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (k X3 (M.op X2 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq110 X0 x X2 X3
       have i₂ := eq88 x X2 X0
       grind)
    | exact superpose eq88 eq110
    | exact resolve eq110 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq110
  have eq174 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq71 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq2820 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq174 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq2828 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2820 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq2820 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq2820 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820
  have eq2865 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ X0) X1
       have i₂ := eq2828 (σ X0)
       grind)
    | exact superpose eq2828 eq29
    | exact resolve eq29 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq2881 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2865 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2865
    | exact resolve eq2865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2865
  have eq2894 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2881 X0 X1
       have i₂ := eq2828 X0
       grind)
    | exact superpose eq2828 eq2881
    | exact resolve eq2881 eq2828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828 eq2881
  have eq2903 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2894 X0 X1
       have i₂ := eq113 X0 X0 X1
       grind)
    | exact superpose eq113 eq2894
    | exact resolve eq2894 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2894
  have eq2908 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2903 X0 X1
       have i₂ := eq113 (σ X0) (σ X0) (σ X1)
       grind)
    | exact superpose eq113 eq2903
    | exact resolve eq2903 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq2903
  have eq3892 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2908 x y
       grind)
    | exact superpose eq2908 eq16
    | (have r₁ := eq16
       have r₂ := eq2908 x y
       grind)
    | exact resolve eq16 eq2908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2908
  have eq3939 : False := by grind
  exact eq3939

/-- `Equation3583`: `x ◇ y = z ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_x_y_y_pxx_pyx_Equation3583 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X2) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) X1) X2 X3
       have i₂ := eq9 X0 X1 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op (M.op X0 X0) X1) X3
       have i₂ := eq9 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op (M.op X0 X0) X1) = (k X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op X0 X0) X1)
       grind)
    | (have r₁ := eq12 (M.op X0 X1) (M.op (M.op X0 X0) X1)
       have r₂ := eq9 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq21 X0 X1 x X3
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq21
    | exact resolve eq21 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq27 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq23 (M.op X0 X0) X1 x
       grind)
    | exact superpose eq23 eq9
    | exact resolve eq9 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq27 X1 X1
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  have eq52 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48
    | (have j0 := eq48 X0
       grind)
    | exact resolve eq48 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq56 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52
    | exact resolve eq52 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X1) (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq22 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq194 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq193
    | exact resolve eq193 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq221 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (k X0 X0)) (σ X0)) X1) = (M.op X2 (M.op (σ (k X0 X0)) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 (σ X0) (σ X0) X2 x
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq20
    | (have j1 := eq33 X0
       grind)
    | exact resolve eq20 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op (σ X0) X1) X2)) = (M.op (M.op (σ (k X0 X0)) X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (σ X0) X1 X2 X3
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq20
    | (have j1 := eq33 X0
       grind)
    | exact resolve eq20 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq227 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (M.op (σ (k X0 X0)) X1) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq224 X0 X1 X2 x
       have i₂ := eq23 (M.op (σ X0) X1) X2 x
       grind)
    | exact superpose eq23 eq224
    | (have j0 := eq224 X0 X1 X2 x
       grind)
    | exact resolve eq224 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq231 : ∀ X0 X1 : G, (M.op (M.op (σ (k X0 X0)) (σ X0)) X1) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq221 X0 X1 x
       have i₂ := eq23 (σ (k X0 X0)) X1 x
       grind)
    | exact superpose eq23 eq221
    | (have j0 := eq221 X0 X1 x
       grind)
    | exact resolve eq221 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq259 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq46 X1 X0
       grind)
    | exact superpose eq46 eq46
    | (have j0 := eq46 X0 X1
       have j1 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op X2 (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (σ X1) (σ X0) x
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq23
    | (have j1 := eq46 X1 X0
       grind)
    | exact resolve eq23 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq272 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq259 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq328 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq40 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq380 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq328 (σ X0)
       grind)
    | exact superpose eq328 eq52
    | exact resolve eq52 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq328
  have eq383 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq380 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq380
    | exact resolve eq380 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq493 : ∀ X0 : G, (k (τ (σ (k X0 X0))) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq383 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq383
    | (have j1 := eq33 X0
       grind)
    | exact resolve eq383 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq383
  have eq509 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq493 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq493
    | (have j0 := eq493 X0
       grind)
    | exact resolve eq493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq513 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq227 (M.op X0 X1)
       have i₂ := eq194 X0 X1
       grind)
    | exact superpose eq194 eq227
    | (have j0 := eq227 (M.op X0 X1)
       grind)
    | exact resolve eq227 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq227 (τ X0)
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq227
    | (have j0 := eq227 (τ X0)
       grind)
    | exact resolve eq227 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq518 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq513 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq519 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq517 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq517
    | (have j0 := eq517 X0
       grind)
    | exact resolve eq517 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq522 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq519 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq519
    | (have j0 := eq519 X0
       grind)
    | exact resolve eq519 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq529 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq522 (τ X0)
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq522
    | (have j0 := eq522 (τ X0)
       grind)
    | exact resolve eq522 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq532 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq556 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq532 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq532
    | (have j0 := eq532 X0
       grind)
    | exact resolve eq532 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq676 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq713 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq676
    | (have j0 := eq676 X0 X1
       grind)
    | exact resolve eq676 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq737 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
       have i₂ := eq518 X0 X1
       grind)
    | exact superpose eq518 eq23
    | exact resolve eq23 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq868 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X0 ∨ (σ (k (τ X0) X2)) = (M.op (σ X2) X0) ∨ (σ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq268 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq268
    | exact resolve eq268 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq268 y x X0
       grind)
    | exact superpose eq268 eq16
    | (have j1 := eq268 y x X0
       grind)
    | exact resolve eq16 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq936 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (M.op X1 X0) = X0 ∨ (σ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq868 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq868
    | (have j0 := eq868 X0 X1 X2
       grind)
    | exact resolve eq868 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq1118 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (τ X0)) X1) X2) = (M.op (M.op (k (σ (τ X0)) X0) X1) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq229 (τ X0) X1 X2
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq229
    | (have j0 := eq229 (τ X0) X1 X2
       grind)
    | exact resolve eq229 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq1180 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (k X0 X0) X1) X2) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1118 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1118
    | (have j0 := eq1118 X0 X1 X2
       grind)
    | exact resolve eq1118 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1187 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1180 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1180
    | (have j0 := eq1180 X0 X1 X2
       grind)
    | exact resolve eq1180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1234 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) X1) = (M.op (M.op (σ (k (τ X0) (τ X0))) X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq231 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq231
    | exact resolve eq231 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq1302 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) X1) = (M.op (M.op (k (σ (τ X0)) X0) X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1234 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq1234
    | (have j0 := eq1234 X0 X1
       grind)
    | exact resolve eq1234 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1310 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (M.op (k X0 X0) X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1302 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1302
    | (have j0 := eq1302 X0 X1
       grind)
    | exact resolve eq1302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1853 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq529 (M.op X0 X1)
       have i₂ := eq194 X0 X1
       grind)
    | exact superpose eq194 eq529
    | (have j0 := eq529 (M.op X0 X1)
       grind)
    | exact resolve eq529 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529
  have eq1862 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1853 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq1907 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq272 X1 X0
       grind)
    | exact superpose eq272 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq272 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq272 X0 X1
       grind)
    | exact resolve eq12 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq1928 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1907 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq1907 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq1907 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1907
  have eq1937 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X0)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1928 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1928
    | (have j0 := eq1928 X0 X1
       grind)
    | exact resolve eq1928 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1928
  have eq1938 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1937 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1937
  have eq1976 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
       have i₂ := eq1862 X0 X1
       grind)
    | exact superpose eq1862 eq23
    | exact resolve eq23 eq1862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1862
  have eq2542 : ∀ X0 : G, (σ (τ X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq509 (τ X0)
       grind)
    | exact superpose eq509 eq19
    | (have j1 := eq509 (τ X0)
       grind)
    | exact resolve eq19 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq2552 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2542 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq2542
    | (have j0 := eq2542 X0
       grind)
    | exact resolve eq2542 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2542
  have eq2573 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2552 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2552
    | (have j0 := eq2552 X0
       grind)
    | exact resolve eq2552 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552
  have eq2583 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2573 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2573
    | (have j0 := eq2573 X0
       grind)
    | exact resolve eq2573 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573
  have eq4449 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq936 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq936
    | (have j0 := eq936 X1 X2 X2
       grind)
    | exact resolve eq936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq4701 : ∀ X0 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (k X0 X0) = X0 ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq194 X2 x
       have i₂ := eq4449 X0 x X2
       grind)
    | exact superpose eq4449 eq194
    | (have j1 := eq4449 X2 X0 X2
       grind)
    | exact resolve eq194 eq4449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq4449
  have eq5074 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1187 X0 X0 X1
       have i₂ := eq1310 X0 X1
       grind)
    | exact superpose eq1310 eq1187
    | (have j0 := eq1187 X0 X1 x
       have j1 := eq1310 X0 X1
       grind)
    | exact resolve eq1187 eq1310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187 eq1310
  have eq5114 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq5074 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5074
  have eq5129 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5114 X0 X1
       have i₂ := eq27 X0 X1
       grind)
    | exact superpose eq27 eq5114
    | (have j0 := eq5114 X0 X1
       grind)
    | exact resolve eq5114 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5114
  have eq5614 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1938 (τ X0) (τ X1)
       have i₂ := eq65 X1 X0
       grind)
    | exact superpose eq65 eq1938
    | (have j0 := eq1938 (τ X0) (τ X1)
       grind)
    | exact resolve eq1938 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq5650 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5614 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5614
    | (have j0 := eq5614 X0 X1
       grind)
    | exact resolve eq5614 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5614
  have eq5658 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5650 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5650
    | (have j0 := eq5650 X0 X1
       grind)
    | exact resolve eq5650 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5650
  have eq5663 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5658 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq5658
    | (have j0 := eq5658 X0 X1
       grind)
    | exact resolve eq5658 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5658
  have eq5666 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5663 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5663
    | (have j0 := eq5663 X0 X1
       grind)
    | exact resolve eq5663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5663
  have eq5667 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5666 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5666
    | (have j0 := eq5666 X0 X1
       grind)
    | exact resolve eq5666 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5666
  have eq5668 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5667 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5667
    | (have j0 := eq5667 X0 X1
       grind)
    | exact resolve eq5667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667
  have eq5669 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5668 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5668
    | (have j0 := eq5668 X0 X1
       grind)
    | exact resolve eq5668 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668
  have eq5690 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5669 (k X0 X0) X0
       have i₂ := eq2583 X0
       grind)
    | exact superpose eq2583 eq5669
    | (have j0 := eq5669 (k X0 X0) X0
       have j1 := eq2583 X0
       grind)
    | (have r₁ := eq5669 (k X0 X0) X0
       have r₂ := eq2583 X0
       grind)
    | exact resolve eq5669 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583 eq5669
  have eq5693 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5690 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5690
  have eq5707 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq5693 X0
       have j1 := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq5693 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq5693 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5693
  have eq6878 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (k X0 (σ (k (τ X0) (τ X0)))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (k (τ X0) (τ X0))
       have i₂ := eq5707 (τ X0)
       grind)
    | exact superpose eq5707 eq18
    | (have j1 := eq5707 (τ X0)
       grind)
    | exact resolve eq18 eq5707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5707
  have eq6913 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6878 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq6878
    | (have j0 := eq6878 X0
       grind)
    | exact resolve eq6878 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq6878
  have eq6942 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq6913 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6913
    | (have j0 := eq6913 X0
       grind)
    | exact resolve eq6913 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6913
  have eq6964 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq6942 X0
       have i₂ := eq65 X0 X0
       grind)
    | exact superpose eq65 eq6942
    | (have j0 := eq6942 X0
       grind)
    | exact resolve eq6942 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq6942
  have eq15079 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq881 X0
       have i₂ := eq713 x y
       grind)
    | exact superpose eq713 eq881
    | (have j0 := eq881 X0
       have j1 := eq713 x y
       grind)
    | (have r₁ := eq881 X0
       have r₂ := eq713 x y
       grind)
    | (have r₁ := eq881 X0
       have r₂ := eq713 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq881 X0
       have r₂ := eq713 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq881 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq881
  have eq15080 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq15079 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15079
  have eq16516 : ∀ X0 : G, (σ (k X0 X0)) = (k (σ X0) (σ (k X0 X0))) ∨ (τ (σ X0)) = (τ (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6964 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq6964
    | exact resolve eq6964 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6964
  have eq16616 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) ∨ (τ (σ X0)) = (τ (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16516 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq16516
    | (have j0 := eq16516 X0
       grind)
    | exact resolve eq16516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16516
  have eq16654 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16616 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq16616
    | (have j0 := eq16616 X0
       grind)
    | exact resolve eq16616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16616
  have eq16692 : ∀ X0 : G, (σ (k X0 X0)) = (σ (k X0 (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16654 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16654
    | (have j0 := eq16654 X0
       grind)
    | exact resolve eq16654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16654
  have eq19049 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op (k X0 X0) X0)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16692 X0
       have i₂ := eq4701 X0 (k X0 X0)
       grind)
    | exact superpose eq4701 eq16692
    | (have j0 := eq16692 X0
       have j1 := eq4701 X0 (k X0 X0)
       grind)
    | exact resolve eq16692 eq4701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4701 eq16692
  have eq19155 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op (k X0 X0) X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq19049 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19049
  have eq21961 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19155 X0
       have i₂ := eq5129 X0 X0
       grind)
    | exact superpose eq5129 eq19155
    | (have j0 := eq19155 X0
       have j1 := eq5129 X0 x
       grind)
    | exact resolve eq19155 eq5129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5129 eq19155
  have eq22111 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq21961 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21961 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq21961 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21961
  have eq22210 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq22111 X0
       grind)
    | exact superpose eq22111 eq10
    | (have j1 := eq22111 X0
       grind)
    | exact resolve eq10 eq22111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22111
  have eq22319 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq22210 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq22210
    | (have j0 := eq22210 X0
       grind)
    | exact resolve eq22210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22210
  have eq22538 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq22319 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq22319
    | exact resolve eq22319 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22319
  have eq322631 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y x) := by
    intro X1
    first
    | (have i₁ := eq1976 x (σ y) x
       have i₂ := eq15080 x
       grind)
    | exact superpose eq15080 eq1976
    | exact resolve eq1976 eq15080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976 eq15080
  have eq322653 : ∀ X1 : G, y = (M.op y x) ∨ y = (M.op X1 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq322631 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq322631
    | exact resolve eq322631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322631
  have eq323529 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ y = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq23 y x x
       have i₂ := eq322653 X1
       grind)
    | exact superpose eq322653 eq23
    | (have j1 := eq322653 X1
       grind)
    | exact resolve eq23 eq322653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322653
  have eq324368 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq323529 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323529
  have eq324369 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq324368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324368
  have eq324522 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X1
    first
    | (have i₁ := eq737 x y x
       have i₂ := eq324369 x
       grind)
    | exact superpose eq324369 eq737
    | exact resolve eq737 eq324369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325404 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq324522 (σ x)
       grind)
    | exact superpose eq324522 eq16
    | exact resolve eq16 eq324522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324522
  have eq326524 : (σ y) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq325404
       have i₂ := eq324369 x
       grind)
    | exact superpose eq324369 eq325404
    | exact resolve eq325404 eq324369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324369 eq325404
  have eq326541 : (σ y) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq326524
  have eq326542 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq326541
  have eq326784 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq326542
       grind)
    | exact superpose eq326542 eq10
    | exact resolve eq10 eq326542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326542
  have eq326924 : x = y ∨ x = y := by
    first
    | (have i₁ := eq326784
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq326784
    | exact resolve eq326784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326784
  have eq326925 : x = y := by grind
  clear eq326924
  have eq326938 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq326925
       grind)
    | exact superpose eq326925 eq16
    | exact resolve eq16 eq326925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326925
  have eq327053 : (σ (k x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq326938
       have i₂ := eq22538 x
       grind)
    | exact superpose eq22538 eq326938
    | (have j1 := eq22538 x
       grind)
    | exact resolve eq326938 eq22538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22538
  have eq328614 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq327053
       have i₂ := eq556 x
       grind)
    | exact superpose eq556 eq327053
    | (have j1 := eq556 x
       grind)
    | (have r₁ := eq327053
       have r₂ := eq556 x
       grind)
    | exact resolve eq327053 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq327053
  have eq328615 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq328614
  have eq328673 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq328615
       grind)
    | exact superpose eq328615 eq10
    | exact resolve eq10 eq328615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328615
  have eq328742 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq328673
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq328673
    | exact resolve eq328673 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328673
  have eq328743 : x = (M.op x x) := by grind
  clear eq328742
  have eq328825 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq23 x x x
       have i₂ := eq328743
       grind)
    | exact superpose eq328743 eq23
    | exact resolve eq23 eq328743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq328832 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq737 x x x
       have i₂ := eq328743
       grind)
    | exact superpose eq328743 eq737
    | exact resolve eq737 eq328743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq328743
  have eq329855 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq326938
       have i₂ := eq328832 (σ x)
       grind)
    | exact superpose eq328832 eq326938
    | exact resolve eq326938 eq328832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326938 eq328832
  have eq329907 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq329855
       have i₂ := eq328825 x
       grind)
    | exact superpose eq328825 eq329855
    | exact resolve eq329855 eq328825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328825 eq329855
  have eq329908 : False := by grind
  exact eq329908
