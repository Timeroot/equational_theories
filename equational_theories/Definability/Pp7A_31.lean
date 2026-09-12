import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2291`: `x = (y ◇ (x ◇ (x ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation2291 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2291 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2291.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X1) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq36 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X1 (M.op X1 X1)) (M.op X0 (M.op X0 X0)))
       have i₂ := eq9 X0 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
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
  have eq45 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq22
    | exact resolve eq22 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq97 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (M.op (τ X1) (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq98 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq97
    | (have j0 := eq97 X0 X1
       grind)
    | exact resolve eq97 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq139 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (M.op (M.op (σ X1) (σ (M.op X1 X1))) (M.op (σ X0) (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (M.op (M.op (σ X1) (σ (M.op X1 X1))) (M.op (σ X0) (σ (M.op X0 X0))))
       have i₂ := eq46 X0 (M.op (σ X1) (σ (M.op X1 X1)))
       grind)
    | exact superpose eq46 eq46
    | exact resolve eq46 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq173 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X0 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq182 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq173 X0 X1 X2
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq173
    | (have j0 := eq173 X0 X1 X2
       grind)
    | exact resolve eq173 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq173
  have eq1400 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (M.op X0 (M.op X0 X0))) ∨ (τ (M.op X1 X1)) = X0 ∨ (σ X0) = (k X1 (σ (M.op (τ X1) (M.op X0 (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq98 (M.op (τ X1) (M.op X0 (M.op X0 X0))) X1
       have i₂ := eq9 X0 (τ X1)
       grind)
    | exact superpose eq9 eq98
    | (have j0 := eq98 (M.op (τ X1) (M.op X0 (M.op X0 X0))) X1
       grind)
    | exact resolve eq98 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq3802 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (k (σ X1) X2)) ≠ (M.op X3 (k (σ X1) X2)) ∨ (k (k (σ X1) X2) X3) = (M.op (σ X0) (k (σ X1) X2)) ∨ (k (σ X1) X2) = X3 ∨ (M.op (σ X0) (k (σ X1) X2)) = (σ (k (k X1 (τ X2)) X0)) ∨ (σ X0) = (k (σ X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq182 X0 X1 X2
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 (k (k (σ X1) X2) X3) (M.op (σ X0) (k (σ X1) X2))
       have j1 := eq182 X1 X2 X0
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq182 X0 X1 X2
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq43545 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = X1 ∨ (τ (M.op X0 X0)) = X1 ∨ (σ X1) = (k X0 (σ (M.op (τ X0) (M.op X1 (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (τ X0)
       have i₂ := eq1400 X1 X0
       grind)
    | exact superpose eq1400 eq9
    | (have j1 := eq1400 X1 X0
       grind)
    | exact resolve eq9 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400
  have eq43549 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = X1 ∨ (τ (M.op X0 X0)) = X1 ∨ (σ X1) = (k X0 (σ (M.op (τ X0) (M.op X1 (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq43545 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq43545
    | (have j0 := eq43545 X0 X1
       grind)
    | exact resolve eq43545 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43545
  have eq43550 : ∀ X0 X1 : G, (σ X1) = (k X0 (σ (M.op (τ X0) (M.op X1 (M.op X1 X1))))) ∨ (τ (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq43549 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43549
  have eq43604 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 (σ (M.op (τ X1) (M.op (τ X0) (τ (M.op X0 X0)))))) ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43550 X1 (τ X0)
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq43550
    | (have j0 := eq43550 X1 (τ X0)
       grind)
    | exact resolve eq43550 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq43713 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (τ (σ (M.op (τ (σ X1)) (M.op X0 (M.op X0 X0)))))) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X1 (σ (M.op (τ (σ X1)) (M.op X0 (M.op X0 X0))))
       have i₂ := eq43550 (σ X1) X0
       grind)
    | exact superpose eq43550 eq37
    | (have j1 := eq43550 (σ X1) X0
       grind)
    | exact resolve eq37 eq43550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq43550
  have eq43919 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (M.op (τ (σ X1)) (M.op X0 (M.op X0 X0)))) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43713 X0 X1
       have i₂ := eq10 (M.op (τ (σ X1)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq10 eq43713
    | (have j0 := eq43713 X0 X1
       grind)
    | exact resolve eq43713 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43713
  have eq43989 : ∀ X0 X1 : G, (k X1 (σ (M.op (τ X1) (M.op (τ X0) (τ (M.op X0 X0)))))) = X0 ∨ (τ X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq43604 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq43604
    | (have j0 := eq43604 X0 X1
       grind)
    | exact resolve eq43604 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43604
  have eq44059 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 (M.op X1 (M.op X0 (M.op X0 X0)))) ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq43919 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq43919
    | (have j0 := eq43919 X0 X1
       grind)
    | exact resolve eq43919 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43919
  have eq44155 : ∀ X0 X1 : G, (k X1 (M.op X1 (M.op X0 (M.op X0 X0)))) = X0 ∨ (τ (M.op (σ X1) (σ X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44059 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq44059
    | (have j0 := eq44059 X0 X1
       grind)
    | exact resolve eq44059 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44059
  have eq44212 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (k X1 (M.op X1 (M.op X0 (M.op X0 X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44155 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44155
    | (have j0 := eq44155 X0 X1
       grind)
    | exact resolve eq44155 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44155
  have eq44255 : ∀ X0 X1 : G, (k X1 (M.op X1 (M.op X0 (M.op X0 X0)))) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq44212 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq44212
    | (have j0 := eq44212 X0 X1
       grind)
    | exact resolve eq44212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44212
  have eq298943 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq3802 X2 X0 X1 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3802
  have eq298944 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq298943 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298943
  have eq298949 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq298944 X0 X1 X2
       have i₂ := eq36 X0 X1 X2
       grind)
    | exact superpose eq36 eq298944
    | (have j0 := eq298944 X0 X1 X2
       grind)
    | exact resolve eq298944 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq298944
  have eq298950 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (σ X2) (k (σ X0) X1)) ∨ (k (σ X0) X1) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq298949 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298949
  have eq299619 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op (σ (τ X0)) (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (k X1 (τ X2))
       have i₂ := eq298950 X1 X2 (τ X0)
       grind)
    | exact superpose eq298950 eq19
    | (have j1 := eq298950 X1 X2 (τ X0)
       grind)
    | exact resolve eq19 eq298950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298950
  have eq300069 : ∀ X0 X1 X2 : G, (k (σ (k X1 (τ X2))) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq299619 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq299619
    | (have j0 := eq299619 X0 X1 X2
       grind)
    | exact resolve eq299619 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299619
  have eq300235 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (σ (τ X0)) = (k (σ X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq300069 X0 X1 X2
       have i₂ := eq19 X2 X1
       grind)
    | exact superpose eq19 eq300069
    | (have j0 := eq300069 X0 X1 X2
       grind)
    | exact resolve eq300069 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300069
  have eq300374 : ∀ X0 X1 X2 : G, (k (k (σ X1) X2) X0) = (M.op X0 (k (σ X1) X2)) ∨ (k (σ X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq300235 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq300235
    | (have j0 := eq300235 X0 X1 X2
       grind)
    | exact resolve eq300235 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300235
  have eq300610 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op X2 (k X0 X1)) ∨ (k X0 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq300374 X0 (τ X0) X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq300374
    | exact resolve eq300374 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300781 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 ∨ (τ X0) = (τ (M.op (σ X1) (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq300374 X0 X1 (σ (M.op (τ (σ X1)) (M.op (τ X0) (τ (M.op X0 X0)))))
       have i₂ := eq43989 X0 (σ X1)
       grind)
    | exact superpose eq43989 eq300374
    | (have j1 := eq43989 X0 (σ X1)
       grind)
    | exact resolve eq300374 eq43989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43989 eq300374
  have eq301781 : ∀ X0 X1 X2 : G, (τ X0) = (τ (σ (M.op X1 X1))) ∨ (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq300781 X0 X1 X2
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq300781
    | (have j0 := eq300781 X0 X1 X2
       grind)
    | exact resolve eq300781 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300781
  have eq301852 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (τ X0) = (M.op X1 X1) ∨ X0 = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301781 X0 X1 X2
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq301781
    | (have j0 := eq301781 X0 X1 X2
       grind)
    | exact resolve eq301781 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301781
  have eq302541 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ X0 = X2 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq300610 X1 (M.op X1 (M.op X0 (M.op X0 X0))) X2
       have i₂ := eq44255 X0 X1
       grind)
    | exact superpose eq44255 eq300610
    | (have j0 := eq300610 X0 X2 (M.op X2 X0)
       have j1 := eq44255 X0 X1
       grind)
    | exact resolve eq300610 eq44255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44255 eq300610
  have eq304024 : ∀ X0 X1 X2 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq302541 X1 X2 (τ X0)
       grind)
    | exact superpose eq302541 eq19
    | (have j1 := eq302541 (k (σ X1) X0) X1 (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq302541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq302541
  have eq306890 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (M.op X2 X2) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq301852 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq301852 eq15
    | (have j1 := eq301852 (σ X1) X2 (σ X0)
       grind)
    | exact resolve eq15 eq301852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301852
  have eq307254 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq306890 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq306890
    | (have j0 := eq306890 X0 X1 X2
       grind)
    | exact resolve eq306890 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306890
  have eq407001 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq304024 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq304024
    | (have j0 := eq304024 X0 X1 X2
       grind)
    | exact resolve eq304024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq304024
  have eq407653 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq407001 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq407001
    | (have j0 := eq407001 X0 X1 X2
       grind)
    | exact resolve eq407001 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407001
  have eq633274 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 X0) = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq307254 x y X0
       grind)
    | exact superpose eq307254 eq16
    | (have j1 := eq307254 x y X0
       grind)
    | exact resolve eq16 eq307254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307254
  have eq636936 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq633274 X0
       have i₂ := eq407653 x y X1
       grind)
    | exact superpose eq407653 eq633274
    | (have j0 := eq633274 X0
       have j1 := eq407653 (M.op X0 X0) y X0
       grind)
    | (have r₁ := eq633274 X0
       have r₂ := eq407653 x y x
       grind)
    | (have r₁ := eq633274 X0
       have r₂ := eq407653 (σ (M.op x y)) (σ (k y x)) x
       grind)
    | (have r₁ := eq633274 X0
       have r₂ := eq407653 (σ (k y x)) (σ (M.op x y)) x
       grind)
    | exact resolve eq633274 eq407653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407653 eq633274
  have eq636953 : ∀ X0 X1 : G, x = y ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq636936 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636936
  have eq636972 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq636953 X0 X1
       grind)
    | exact superpose eq636953 eq16
    | (have j1 := eq636953 X0 X0
       grind)
    | exact resolve eq16 eq636953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636953
  have eq636973 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq636972 X0 X0
       grind)
    | (have r₁ := eq636972 X0 X1
       have r₂ := eq22 x
       grind)
    | exact resolve eq636972 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636972
  have eq639797 : ∀ X0 X1 : G, y = (τ (σ x)) ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 y
       have i₂ := eq636973 X0 X1
       grind)
    | exact superpose eq636973 eq10
    | (have j1 := eq636973 X0 X0
       grind)
    | exact resolve eq10 eq636973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636973
  have eq640403 : ∀ X0 X1 : G, x = y ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq639797 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq639797
    | (have j0 := eq639797 X0 X0
       grind)
    | exact resolve eq639797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639797
  have eq640405 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq640403 X0 X1
       grind)
    | exact superpose eq640403 eq16
    | (have j1 := eq640403 X0 X0
       grind)
    | exact resolve eq16 eq640403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640403
  have eq640406 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq640405 X0 X0
       grind)
    | (have r₁ := eq640405 X0 X1
       have r₂ := eq22 x
       grind)
    | exact resolve eq640405 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq640405
  have eq644503 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq640406 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640406
  have eq644504 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq644503 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644503
  have eq645100 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq42 X0 X0
       have i₂ := eq644504 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq644504 eq42
    | exact resolve eq42 eq644504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq645101 : ∀ X0 : G, (σ X0) = (M.op (σ X0) y) := by
    intro X0
    first
    | (have i₁ := eq139 X0 X0
       have i₂ := eq644504 (M.op (σ X0) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq644504 eq139
    | exact resolve eq139 eq644504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq645186 : ∀ X0 X1 : G, (σ y) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq644504 (k (τ X0) X1)
       grind)
    | exact superpose eq644504 eq44
    | exact resolve eq44 eq644504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq645234 : y = (σ y) := by
    first
    | (have i₁ := eq645186 x x
       have i₂ := eq644504 (k x (σ x))
       grind)
    | exact superpose eq644504 eq645186
    | exact resolve eq645186 eq644504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644504 eq645186
  have eq655011 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq645234
       grind)
    | exact superpose eq645234 eq16
    | exact resolve eq16 eq645234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645234
  have eq655892 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq655011
       have i₂ := eq645101 x
       grind)
    | exact superpose eq645101 eq655011
    | exact resolve eq655011 eq645101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645101 eq655011
  have eq656220 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq655892
       have i₂ := eq645100 x
       grind)
    | exact superpose eq645100 eq655892
    | exact resolve eq655892 eq645100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq645100 eq655892
  have eq656221 : False := by grind
  exact eq656221

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_x_pyx_x_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq17
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq20
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq65 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X1 (σ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq29
    | exact resolve eq29 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq128 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq65
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq226 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq128 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq128
    | exact resolve eq128 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq505 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq226 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq226
    | exact resolve eq226 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq590 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq590 X0
       grind)
    | exact superpose eq590 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X0) ≠ (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq593 X0 X1
       have i₂ := eq590 X1
       grind)
    | exact superpose eq590 eq593
    | (have j0 := eq593 X0 X1
       grind)
    | (have r₁ := eq593 X0 X0
       have r₂ := eq590 X0
       grind)
    | exact resolve eq593 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq840 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq505 (σ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq505
    | exact resolve eq505 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq505
  have eq2200 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ y = (M.op x y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq9
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq9 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2206 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2208 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2206 X0 X1
       have i₂ := eq590 X1
       grind)
    | exact superpose eq590 eq2206
    | (have j0 := eq2206 X0 X1
       grind)
    | exact resolve eq2206 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2212 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq2200
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq2200
    | exact resolve eq2200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200
  have eq2213 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (k X0 X0) = (k X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2208 X0 X1
       have i₂ := eq590 X0
       grind)
    | exact superpose eq590 eq2208
    | (have j0 := eq2208 X0 X1
       grind)
    | exact resolve eq2208 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2208
  have eq2217 : (M.op y y) = (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2212
       have i₂ := eq590 x
       grind)
    | exact superpose eq590 eq2212
    | exact resolve eq2212 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212
  have eq2218 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k x x) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2217
       have i₂ := eq590 y
       grind)
    | exact superpose eq590 eq2217
    | exact resolve eq2217 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq2219 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k x x) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2218
       have i₂ := eq11 (σ y) (σ x)
       grind)
    | exact superpose eq11 eq2218
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | (have r₁ := eq2218
       have r₂ := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq2218 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218
  have eq2220 : (k x x) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq2219
  have eq2221 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2220
       have i₂ := eq590 (σ x)
       grind)
    | exact superpose eq590 eq2220
    | exact resolve eq2220 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq2222 : (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2221
       have i₂ := eq590 (σ y)
       grind)
    | exact superpose eq590 eq2221
    | exact resolve eq2221 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq2294 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2222
       grind)
    | exact superpose eq2222 eq10
    | exact resolve eq10 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq2295 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2294
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2294
    | exact resolve eq2294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294
  have eq2296 : y = (M.op x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2295
  have eq2371 : y ≠ y ∨ (M.op y y) = (M.op x x) ∨ y = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2296
       grind)
    | exact superpose eq2296 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2296
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2296
       grind)
    | exact resolve eq12 eq2296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq2373 : (M.op y y) = (M.op x x) ∨ y = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2371
  have eq2375 : (M.op y y) = (k x x) ∨ y = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2373
       have i₂ := eq590 x
       grind)
    | exact superpose eq590 eq2373
    | exact resolve eq2373 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2373
  have eq2377 : y = (k y x) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2375
       have i₂ := eq590 y
       grind)
    | exact superpose eq590 eq2375
    | exact resolve eq2375 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2655 : (k x x) = (k y y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y x
       have i₂ := eq2377
       grind)
    | exact superpose eq2377 eq10
    | exact resolve eq10 eq2377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2377
  have eq2992 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq2655
       grind)
    | exact superpose eq2655 eq10
    | exact resolve eq10 eq2655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655
  have eq2996 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2992
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq2992
    | exact resolve eq2992 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq2997 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq2996
  have eq3073 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq2997
       grind)
    | exact superpose eq2997 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2997
       grind)
    | exact resolve eq12 eq2997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997
  have eq3075 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3073
  have eq3076 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3075
  have eq3079 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3076
       have i₂ := eq590 (σ x)
       grind)
    | exact superpose eq590 eq3076
    | exact resolve eq3076 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3076
  have eq3082 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3079
       have i₂ := eq590 (σ y)
       grind)
    | exact superpose eq590 eq3079
    | exact resolve eq3079 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq3079
  have eq3083 : (σ y) = (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3082
  have eq3116 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq840 x (σ y)
       have i₂ := eq3083
       grind)
    | exact superpose eq3083 eq840
    | exact resolve eq840 eq3083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq3119 : y = (k y x) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3116
       have i₂ := eq15 y
       grind)
    | exact superpose eq15 eq3116
    | exact resolve eq3116 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3116
  have eq3342 : y ≠ y ∨ (k x x) = (k y y) ∨ y = (M.op x y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2213 x y
       have i₂ := eq3119
       grind)
    | exact superpose eq3119 eq2213
    | (have j0 := eq2213 x y
       grind)
    | (have r₁ := eq2213 x y
       have r₂ := eq3119
       grind)
    | exact resolve eq2213 eq3119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq3344 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2213 (σ x) (σ y)
       have i₂ := eq3083
       grind)
    | exact superpose eq3083 eq2213
    | (have j0 := eq2213 (σ x) (σ y)
       grind)
    | (have r₁ := eq2213 (σ x) (σ y)
       have r₂ := eq3083
       grind)
    | exact resolve eq2213 eq3083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213 eq3083
  have eq3347 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3344
  have eq3348 : (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3347
  have eq3351 : y = (M.op x y) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3342
  have eq3589 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq3351
       grind)
    | exact superpose eq3351 eq9
    | exact resolve eq9 eq3351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3351
  have eq3597 : (k x x) = (k y y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have r₁ := eq3589
       have r₂ := eq3348
       grind)
    | exact resolve eq3589 eq3348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3348 eq3589
  have eq3608 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq3597
       grind)
    | exact superpose eq3597 eq10
    | exact resolve eq10 eq3597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3597
  have eq3613 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3608
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq3608
    | exact resolve eq3608 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3608
  have eq3614 : (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq3613
  have eq3617 : (k y y) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq17 y y
       have i₂ := eq3614
       grind)
    | exact superpose eq3614 eq17
    | exact resolve eq17 eq3614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3682 : (k x x) = (k y y) := by
    first
    | (have i₁ := eq3617
       have i₂ := eq17 x x
       grind)
    | exact superpose eq17 eq3617
    | exact resolve eq3617 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq3617
  have eq5905 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq594 y x
       grind)
    | exact superpose eq594 eq9
    | (have j1 := eq594 x y
       grind)
    | exact resolve eq9 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5920 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq5905
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq5905
    | exact resolve eq5905 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5905
  have eq5954 : (k x x) ≠ (k x x) ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5920
       have i₂ := eq3682
       grind)
    | exact superpose eq3682 eq5920
    | (have r₁ := eq5920
       have r₂ := eq3682
       grind)
    | exact resolve eq5920 eq3682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3682 eq5920
  have eq5955 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by grind
  clear eq5954
  have eq5991 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq5955
       have i₂ := eq594 (σ y) (σ x)
       grind)
    | exact superpose eq594 eq5955
    | (have j1 := eq594 (σ x) (σ y)
       grind)
    | (have r₁ := eq5955
       have r₂ := eq594 (σ y) (σ x)
       grind)
    | exact resolve eq5955 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq5955
  have eq5995 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq5991
  have eq5997 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq5995
       have i₂ := eq3614
       grind)
    | exact superpose eq3614 eq5995
    | (have r₁ := eq5995
       have r₂ := eq3614
       grind)
    | exact resolve eq5995 eq3614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3614 eq5995
  have eq5998 : False := by grind
  exact eq5998

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_x_y_pxy_pxx_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq75 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq90 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq15
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq90
    | exact resolve eq90 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq90
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq101 X0
       have i₂ := eq14 (σ X0) X1
       grind)
    | exact superpose eq14 eq101
    | (have j1 := eq14 (σ X0) X1
       grind)
    | exact resolve eq101 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq118 X0 X1
       grind)
    | (have r₁ := eq134 X0 X1
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq134 X0 (σ (M.op X0 X0))
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq134 (M.op X0 X0) (σ X0)
       have r₂ := eq118 X0 X1
       grind)
    | exact resolve eq134 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq134
  have eq163 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq141 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141
    | exact resolve eq141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq141 X0 (σ X1)
       grind)
    | exact superpose eq141 eq15
    | (have j1 := eq141 (k X0 X1) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq176 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq163 (τ X0) X1
       grind)
    | exact superpose eq163 eq18
    | (have j1 := eq163 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq163
  have eq259 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq176 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq176
    | exact resolve eq176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq282 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq259 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq259
    | (have j0 := eq259 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq860 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq167 x y
       grind)
    | exact superpose eq167 eq16
    | (have j1 := eq167 x y
       grind)
    | exact resolve eq16 eq167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq874 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq860
       have i₂ := eq282 x y
       grind)
    | exact superpose eq282 eq860
    | (have j1 := eq282 (σ x) (σ y)
       grind)
    | (have r₁ := eq860
       have r₂ := eq282 x y
       grind)
    | (have r₁ := eq860
       have r₂ := eq282 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq860
       have r₂ := eq282 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq860 eq282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq860
  have eq875 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq874
  have eq877 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq875
       grind)
    | exact superpose eq875 eq16
    | exact resolve eq16 eq875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq875
  have eq878 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq877
       have r₂ := eq101 x
       grind)
    | exact resolve eq877 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877
  have eq879 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq878
       grind)
    | exact superpose eq878 eq16
    | exact resolve eq16 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq878
       grind)
    | exact superpose eq878 eq10
    | exact resolve eq10 eq878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq921 : x = y := by
    first
    | (have i₁ := eq880
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq880
    | exact resolve eq880 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq922 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq879
       have i₂ := eq101 x
       grind)
    | exact superpose eq101 eq879
    | exact resolve eq879 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq879
  have eq923 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq922
       have i₂ := eq921
       grind)
    | exact superpose eq921 eq922
    | exact resolve eq922 eq921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq922
  have eq924 : False := by grind
  exact eq924

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_x_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq59 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq180 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq59 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq12
    | (have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq12 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq192 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq197 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq192 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq192
    | (have j0 := eq192 X0 X1
       grind)
    | exact resolve eq192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq198 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq316 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq198
    | exact resolve eq198 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq198 x y
       grind)
    | exact superpose eq198 eq16
    | (have j1 := eq198 x y
       grind)
    | exact resolve eq16 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq337 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq316
    | (have j0 := eq316 X0 X1
       grind)
    | exact resolve eq316 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq316
  have eq359 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq337
    | exact resolve eq337 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq459 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq322
       have i₂ := eq359 x y
       grind)
    | exact superpose eq359 eq322
    | (have j1 := eq359 (σ x) (σ y)
       grind)
    | (have r₁ := eq322
       have r₂ := eq359 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq322
       have r₂ := eq359 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq322 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq359
  have eq462 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq459
  have eq501 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq462
       grind)
    | exact superpose eq462 eq10
    | exact resolve eq10 eq462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq534 : x = y ∨ x = y := by
    first
    | (have i₁ := eq501
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq501
    | exact resolve eq501 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq535 : x = y := by grind
  clear eq534
  have eq537 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq535
       grind)
    | exact superpose eq535 eq16
    | exact resolve eq16 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq538 : False := by grind
  exact eq538

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyy_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
       have r₂ := eq12 x x
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
  have eq59 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq54 (τ X0)
       grind)
    | exact superpose eq54 eq18
    | exact resolve eq18 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq59 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq59
    | exact resolve eq59 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
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
  clear eq56
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq62 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq62
    | exact resolve eq62 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq62
  have eq79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq239 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq90
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq267 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq239 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq239
    | (have j0 := eq239 X0 X1
       grind)
    | exact resolve eq239 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq239
  have eq271 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq267 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq267 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq274 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq271 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq271
    | (have j0 := eq271 X0 X1
       grind)
    | exact resolve eq271 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq358 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq274
    | exact resolve eq274 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq274 (σ X0) X1
       grind)
    | exact superpose eq274 eq15
    | (have j1 := eq274 (σ X0) X1
       grind)
    | exact resolve eq15 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq383 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq365
    | (have j0 := eq365 X0 X1
       grind)
    | exact resolve eq365 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq365
  have eq407 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq358 (τ X1) X0
       grind)
    | exact superpose eq358 eq17
    | (have j1 := eq358 (τ X1) X0
       grind)
    | exact resolve eq17 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq358
  have eq847 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq407
    | exact resolve eq407 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407
  have eq897 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq847 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq847
    | (have j0 := eq847 X0 X1
       grind)
    | exact resolve eq847 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq3840 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq383 x y
       grind)
    | exact superpose eq383 eq16
    | (have j1 := eq383 x y
       grind)
    | exact resolve eq16 eq383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3870 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq383 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq3912 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3840
       have i₂ := eq897 y x
       grind)
    | exact superpose eq897 eq3840
    | (have j1 := eq897 y x
       grind)
    | (have r₁ := eq3840
       have r₂ := eq897 y x
       grind)
    | exact resolve eq3840 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq3840
  have eq3913 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3912
  have eq3918 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ y = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq3913
       grind)
    | exact superpose eq3913 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3913
       grind)
    | exact resolve eq13 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3925 : y = (M.op y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq3918
  have eq4055 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq3870 (τ X1) (τ X0)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq3870
    | (have j0 := eq3870 (τ X1) (τ X0)
       grind)
    | exact resolve eq3870 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq4104 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4055 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq4055
    | (have j0 := eq4055 X0 X1
       grind)
    | exact resolve eq4055 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4055
  have eq4125 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4104 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4104
    | (have j0 := eq4104 X0 X1
       grind)
    | exact resolve eq4104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104
  have eq4139 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4125 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4125
    | (have j0 := eq4125 X0 X1
       grind)
    | exact resolve eq4125 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4125
  have eq4150 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4139 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4139
    | (have j0 := eq4139 X0 X1
       grind)
    | exact resolve eq4139 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq4155 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4150 X0 X1
       have i₂ := eq68 X1
       grind)
    | exact superpose eq68 eq4150
    | (have j0 := eq4150 X0 X1
       grind)
    | exact resolve eq4150 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq4150
  have eq15158 : y ≠ y ∨ (M.op x y) = (k y x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3925
       grind)
    | exact superpose eq3925 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3925
       grind)
    | exact resolve eq12 eq3925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3925
  have eq15166 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by grind
  clear eq15158
  have eq62095 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15166
       grind)
    | exact superpose eq15166 eq16
    | exact resolve eq16 eq15166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15166
  have eq62154 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq62095
       have i₂ := eq3913
       grind)
    | exact superpose eq3913 eq62095
    | exact resolve eq62095 eq3913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3913 eq62095
  have eq62155 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq62154
  have eq62156 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq62155
  have eq62509 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq79 x (σ y)
       have i₂ := eq62156
       grind)
    | exact superpose eq62156 eq79
    | (have j0 := eq79 x (σ y)
       grind)
    | (have r₁ := eq79 x (σ y)
       have r₂ := eq62156
       grind)
    | exact resolve eq79 eq62156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq62547 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq62509
  have eq62559 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq62547
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq62547
    | exact resolve eq62547 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62547
  have eq89645 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq62559
       grind)
    | exact superpose eq62559 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq62559
       grind)
    | exact resolve eq12 eq62559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62559
  have eq89666 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by grind
  clear eq89645
  have eq89687 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq89666
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq89666
    | exact resolve eq89666 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89666
  have eq740264 : (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq62156
       have i₂ := eq89687
       grind)
    | exact superpose eq89687 eq62156
    | exact resolve eq62156 eq89687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62156 eq89687
  have eq740489 : (k y x) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq740264
  have eq743655 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3870 x y
       have i₂ := eq740489
       grind)
    | exact superpose eq740489 eq3870
    | (have j0 := eq3870 x y
       grind)
    | (have r₁ := eq3870 x y
       have r₂ := eq740489
       grind)
    | exact resolve eq3870 eq740489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq743658 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4155 y x
       have i₂ := eq740489
       grind)
    | exact superpose eq740489 eq4155
    | (have j0 := eq4155 y x
       grind)
    | (have r₁ := eq4155 y x
       have r₂ := eq740489
       grind)
    | exact resolve eq4155 eq740489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740489
  have eq743883 : (M.op x y) = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq743658
  have eq743885 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq743655
  have eq743894 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq3870 x y
       grind)
    | (have r₁ := eq743885
       have r₂ := eq3870 x y
       grind)
    | exact resolve eq743885 eq3870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3870 eq743885
  have eq743925 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq743894
       grind)
    | exact superpose eq743894 eq16
    | exact resolve eq16 eq743894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743894
  have eq746999 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq743925
       have i₂ := eq743883
       grind)
    | exact superpose eq743883 eq743925
    | exact resolve eq743925 eq743883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743883
  have eq747018 : (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq746999
  have eq750110 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq747018
       grind)
    | exact superpose eq747018 eq10
    | exact resolve eq10 eq747018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747018
  have eq750627 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq750110
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq750110
    | exact resolve eq750110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750110
  have eq750678 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4155 y x
       have i₂ := eq750627
       grind)
    | exact superpose eq750627 eq4155
    | (have j0 := eq4155 y x
       grind)
    | (have r₁ := eq4155 y x
       have r₂ := eq750627
       grind)
    | exact resolve eq4155 eq750627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4155 eq750627
  have eq750903 : (M.op x y) = (M.op x x) := by grind
  clear eq750678
  have eq753921 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq743925
       have i₂ := eq750903
       grind)
    | exact superpose eq750903 eq743925
    | exact resolve eq743925 eq750903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743925 eq750903
  have eq753940 : False := by grind
  exact eq753940

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyx_pxx_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X0) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X0))) (M.op X0 X0)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X1 (M.op X0 (M.op X1 X0)))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
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
  have eq100 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq62
  have eq104 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq100 X0 x
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq100
    | (have j0 := eq100 X0 x
       grind)
    | exact resolve eq100 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq104 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq104 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq104 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq108 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq105 (σ X0)
       grind)
    | exact superpose eq105 eq15
    | exact resolve eq15 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq108
    | exact resolve eq108 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq108
  have eq812 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq848 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq812 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq812
    | (have j0 := eq812 X0 X1
       grind)
    | exact resolve eq812 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq4375 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq16
    | (have j1 := eq91 x y
       grind)
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq6313 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq4375
       have i₂ := eq848 y x
       grind)
    | exact superpose eq848 eq4375
    | (have j1 := eq848 (σ y) (σ x)
       grind)
    | (have r₁ := eq4375
       have r₂ := eq848 y x
       grind)
    | (have r₁ := eq4375
       have r₂ := eq848 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq4375
       have r₂ := eq848 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq4375 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6314 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq6313
  have eq6316 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6314
       grind)
    | exact superpose eq6314 eq16
    | exact resolve eq16 eq6314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6314
  have eq6317 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6316
       have r₂ := eq119 x
       grind)
    | exact resolve eq6316 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6316
  have eq6319 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6317
       grind)
    | exact superpose eq6317 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6317
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6317
       grind)
    | exact resolve eq12 eq6317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6317
  have eq6323 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq6319
  have eq6324 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4375
       have i₂ := eq6323
       grind)
    | exact superpose eq6323 eq4375
    | exact resolve eq4375 eq6323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4375 eq6323
  have eq6325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq6324
  have eq6326 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq6325
  have eq6332 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq6326
       grind)
    | exact superpose eq6326 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6326
       grind)
    | exact resolve eq12 eq6326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6326
  have eq6336 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq6332
  have eq6343 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6336
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6336
    | exact resolve eq6336 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6336
  have eq6355 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6343
       grind)
    | exact superpose eq6343 eq16
    | exact resolve eq16 eq6343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6343
  have eq6412 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq6355
       have i₂ := eq848 y x
       grind)
    | exact superpose eq848 eq6355
    | (have j1 := eq848 y x
       grind)
    | (have r₁ := eq6355
       have r₂ := eq848 y x
       grind)
    | (have r₁ := eq6355
       have r₂ := eq848 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6355
       have r₂ := eq848 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6355 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq6413 : x = y ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by grind
  clear eq6412
  have eq6417 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6413
       grind)
    | exact superpose eq6413 eq16
    | exact resolve eq16 eq6413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6413
  have eq6418 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6417
       have r₂ := eq119 x
       grind)
    | exact resolve eq6417 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6417
  have eq6420 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6418
       grind)
    | exact superpose eq6418 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6418
       grind)
    | exact resolve eq12 eq6418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6418
  have eq6424 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq6420
  have eq6425 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6355
       have i₂ := eq6424
       grind)
    | exact superpose eq6424 eq6355
    | exact resolve eq6355 eq6424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6355 eq6424
  have eq6429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq6425
  have eq6430 : (σ x) = (σ y) := by grind
  clear eq6429
  have eq6431 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6430
       grind)
    | exact superpose eq6430 eq16
    | exact resolve eq16 eq6430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6432 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6430
       grind)
    | exact superpose eq6430 eq10
    | exact resolve eq10 eq6430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6430
  have eq6485 : x = y := by
    first
    | (have i₁ := eq6432
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6432
    | exact resolve eq6432 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6432
  have eq6486 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6431
       have i₂ := eq119 x
       grind)
    | exact superpose eq119 eq6431
    | exact resolve eq6431 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq6431
  have eq6489 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6486
       have i₂ := eq6485
       grind)
    | exact superpose eq6485 eq6486
    | exact resolve eq6486 eq6485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6485 eq6486
  have eq6490 : False := by grind
  exact eq6490

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq73
    | exact resolve eq73 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq73
  have eq99 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq99 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq99
    | exact resolve eq99 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq100
  have eq151 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq156 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq151
    | (have j0 := eq151 X0 X1
       grind)
    | exact resolve eq151 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq790 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq156 x y
       grind)
    | exact superpose eq156 eq16
    | (have j1 := eq156 x y
       grind)
    | exact resolve eq16 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq1090 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq153
    | exact resolve eq153 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq1149 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1090 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1090
    | (have j0 := eq1090 X0 X1
       grind)
    | exact resolve eq1090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq4027 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq790
       have i₂ := eq1149 y x
       grind)
    | exact superpose eq1149 eq790
    | (have j1 := eq1149 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq790
       have r₂ := eq1149 y x
       grind)
    | (have r₁ := eq790
       have r₂ := eq1149 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq790
       have r₂ := eq1149 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq790 eq1149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790 eq1149
  have eq4028 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq4027
  have eq4693 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4028
       grind)
    | exact superpose eq4028 eq16
    | exact resolve eq16 eq4028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028
  have eq4694 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4693
       have r₂ := eq80 x
       grind)
    | exact resolve eq4693 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4693
  have eq4700 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq4694
       grind)
    | exact superpose eq4694 eq103
    | exact resolve eq103 eq4694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4694
  have eq4716 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4700
       have r₂ := eq16
       grind)
    | exact resolve eq4700 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4700
  have eq4719 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4716
       grind)
    | exact superpose eq4716 eq10
    | exact resolve eq10 eq4716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4716
  have eq4768 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4719
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4719
    | exact resolve eq4719 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4771 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4768
       grind)
    | exact superpose eq4768 eq16
    | exact resolve eq16 eq4768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4768
  have eq4772 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4771
       have r₂ := eq80 x
       grind)
    | exact resolve eq4771 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq4771
  have eq4779 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq4772
       grind)
    | exact superpose eq4772 eq10
    | exact resolve eq10 eq4772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4772
  have eq4828 : y = (M.op x x) := by
    first
    | (have i₁ := eq4779
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4779
    | exact resolve eq4779 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779
  have eq4840 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq4828
       grind)
    | exact superpose eq4828 eq103
    | exact resolve eq103 eq4828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq4828
  have eq4856 : False := by grind
  exact eq4856

/-- `Equation2300`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation2300 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2300 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2300.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq21 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq21 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq21 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq30 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq26 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq32 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq32 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq42 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq35 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq35 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       have j1 := eq36 X1 X0
       grind)
    | (have r₁ := eq42 X1 X0
       have r₂ := eq36 X0 X1
       grind)
    | exact resolve eq42 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq42
  have eq47 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45
  have eq94 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq98 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       have j1 := eq47 X0 X1
       grind)
    | (have r₁ := eq94 X0 X1
       have r₂ := eq47 X0 X1
       grind)
    | (have r₁ := eq94 X1 X1
       have r₂ := eq47 X1 X1
       grind)
    | exact resolve eq94 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq94
  have eq231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq98 (σ X0) (σ X1)
       grind)
    | exact superpose eq98 eq15
    | exact resolve eq15 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq231 X0 X1
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq231
    | exact resolve eq231 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq231
  have eq241 : False := by grind
  exact eq241
