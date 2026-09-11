import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq175 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq391 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq307
    | exact resolve eq307 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq175 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq538 X1 X0
       grind)
    | exact superpose eq538 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq538 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq538 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq538 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq538 (M.op X1 X1) X0
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq558 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq957 : ∀ X0 X1 X2 : G, (M.op (k X0 (M.op X1 X1)) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq929 X0 X1
       grind)
    | exact superpose eq929 eq16
    | exact resolve eq16 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1465 : (M.op y y) = (M.op y x) ∨ (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq1466 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1505 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq538 X0 X1
       grind)
    | exact superpose eq538 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq538 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq538 X1 X1
       grind)
    | exact resolve eq12 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1519 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1520 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1505 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505
  have eq1524 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1519 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1519 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1519 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq1606 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (k X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X1 X0 X2
       have i₂ := eq1524 X0
       grind)
    | exact superpose eq1524 eq175
    | exact resolve eq175 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1610 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq1524 X0
       grind)
    | exact superpose eq1524 eq538
    | exact resolve eq538 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq1620 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq567 X0 X2 X1
       have i₂ := eq1524 X0
       grind)
    | exact superpose eq1524 eq567
    | exact resolve eq567 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq1623 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (k X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 X0
       have i₂ := eq1524 X0
       grind)
    | exact superpose eq1524 eq929
    | exact resolve eq929 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1628 : ∀ X0 X1 X2 : G, (M.op (k X1 (k X0 X0)) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq957 X1 X0 X2
       have i₂ := eq1524 X0
       grind)
    | exact superpose eq1524 eq957
    | exact resolve eq957 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq1667 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1620 X0 X1 X2
       have i₂ := eq1623 X0 (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq1623 eq1620
    | exact resolve eq1620 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620
  have eq1688 : ∀ X0 X1 X2 : G, (k (M.op X1 (k X2 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1667 X0 X1 X2
       have i₂ := eq1524 X2
       grind)
    | exact superpose eq1524 eq1667
    | exact resolve eq1667 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1667
  have eq1782 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1610 (σ X1) X0
       grind)
    | exact superpose eq1610 eq10
    | exact resolve eq10 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2043 : ∀ X0 X2 : G, (M.op (σ (k X0 X0)) X2) = (k X2 (σ (k X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq929 X0 X0
       have i₂ := eq1782 X0 x
       grind)
    | exact superpose eq1782 eq929
    | exact resolve eq929 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2063 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X1 X2 (M.op X1 (M.op X2 X2))
       have i₂ := eq1782 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact superpose eq1782 eq175
    | exact resolve eq175 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2073 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X0)) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq1782 (M.op X1 X1) X0
       grind)
    | exact superpose eq1782 eq16
    | exact resolve eq16 eq1782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1782
  have eq2113 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X0)) (M.op X2 (k X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2073 X0 X1 X2
       have i₂ := eq1524 X1
       grind)
    | exact superpose eq1524 eq2073
    | exact resolve eq2073 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073
  have eq2118 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X2)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2063 X0 X1 X2
       have i₂ := eq1524 X2
       grind)
    | exact superpose eq1524 eq2063
    | exact resolve eq2063 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063
  have eq2172 : ∀ X0 X1 X2 : G, (k (M.op X2 (k X1 X1)) (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2113 X0 X1 X2
       have i₂ := eq2043 X0 (M.op X2 (k X1 X1))
       grind)
    | exact superpose eq2043 eq2113
    | exact resolve eq2113 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043 eq2113
  have eq5561 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 X3))) X1) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq178 X2 x X3 X4
       have i₂ := eq178 X1 X0 (M.op X2 X3) x
       grind)
    | (have i₁ := eq178 X0 (M.op (M.op X0 X2) (M.op X0 X2)) X2 X3
       have i₂ := eq178 (M.op X0 X2) (M.op X0 X2) (M.op X0 X2) X3
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq5761 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (k (M.op X1 (M.op X2 X3)) (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5561 X0 X1 X2 X3 X4
       have i₂ := eq929 (M.op X1 (M.op X2 X3)) X0
       grind)
    | exact superpose eq929 eq5561
    | exact resolve eq5561 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq5561
  have eq5888 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (k (M.op X1 (M.op X2 X3)) (k X0 X0)) X1) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5761 X0 X1 X2 X3 X4
       have i₂ := eq1524 X0
       grind)
    | exact superpose eq1524 eq5761
    | exact resolve eq5761 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5761
  have eq5981 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (k (M.op X1 (M.op X2 X3)) (k X0 X0)) X1) X2) = (M.op (k X4 X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5888 X0 X1 X2 X3 X4
       have i₂ := eq1524 X4
       grind)
    | exact superpose eq1524 eq5888
    | exact resolve eq5888 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5888
  have eq14704 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq14706 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14704 X0 X1
       have i₂ := eq1524 X0
       grind)
    | exact superpose eq1524 eq14704
    | (have j0 := eq14704 X0 X1
       grind)
    | exact resolve eq14704 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14704
  have eq14937 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14706 X1 (τ X0)
       have i₂ := eq391 X0 X0
       grind)
    | exact superpose eq391 eq14706
    | (have j0 := eq14706 X1 (τ X0)
       grind)
    | exact resolve eq14706 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq18237 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ (M.op X0 (k X1 X1))) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq307 (M.op X0 (k X1 X1)) (k X2 X2)
       have i₂ := eq2172 X2 X1 X0
       grind)
    | exact superpose eq2172 eq307
    | exact resolve eq307 eq2172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq2172
  have eq150503 : ∀ X0 X1 X3 : G, (M.op (τ X0) (M.op X3 (τ (M.op X0 (k X1 X1))))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1628 x (τ (M.op X0 (k X1 X1))) X3
       have i₂ := eq18237 X0 X1 x
       grind)
    | exact superpose eq18237 eq1628
    | exact resolve eq1628 eq18237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628 eq18237
  have eq268698 : ∀ X0 X1 : G, (M.op x (M.op X0 (τ (M.op (σ x) (k X1 X1))))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq29 eq150503
    | exact resolve eq150503 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150503
  have eq269987 : ∀ X0 X1 : G, (τ (M.op (σ x) (k X1 X1))) = (M.op x (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq268698 (τ (M.op sF2 (k X1 X1))) X1
       have i₂ := eq1610 X0 (τ (M.op sF2 (k X1 X1)))
       grind)
    | exact superpose eq1610 eq268698
    | exact resolve eq268698 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610 eq268698
  have eq271240 : ∀ X0 X1 : G, (M.op (σ x) (k X1 X1)) = (σ (M.op x (k X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq269987 eq14
    | exact resolve eq14 eq269987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269987
  have eq272589 : ∀ X0 X2 : G, (σ (M.op x (k X0 X0))) = (M.op (σ x) (σ (k X2 X2))) := by
    intro X0 X2
    first
    | exact superpose eq271240 eq2118
    | exact resolve eq2118 eq271240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118 eq271240
  have eq329865 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (k X0 (k X3 X3)) X1) X0) = (M.op (k X4 X4) (M.op X1 (k X2 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5981 X3 X1 X0 (M.op X1 (k X2 X2)) X4
       have i₂ := eq1606 X2 X1 X0
       grind)
    | exact superpose eq1606 eq5981
    | exact resolve eq5981 eq1606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606 eq5981
  have eq331350 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (k X0 (k X3 X3)) X1) X0) = (k (M.op X1 (k X2 X2)) (k X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq329865 X0 X1 X2 X3 X4
       have i₂ := eq1623 X4 (M.op X1 (k X2 X2))
       grind)
    | exact superpose eq1623 eq329865
    | exact resolve eq329865 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623 eq329865
  have eq331899 : ∀ X0 X1 X3 : G, (M.op (M.op (k X0 (k X3 X3)) X1) X0) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq331350 X0 X1 x X3 x
       have i₂ := eq1688 x X1 x
       grind)
    | exact superpose eq1688 eq331350
    | exact resolve eq331350 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331350
  have eq332477 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (k X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq331899 (M.op X0 (k X1 X1)) X3 x
       have i₂ := eq1688 x X0 X1
       grind)
    | exact superpose eq1688 eq331899
    | exact resolve eq331899 eq1688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1688 eq331899
  have eq333352 : ∀ X0 : G, y = (M.op (M.op y x) (M.op y (k X0 X0))) ∨ (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq332477 y X0 y
       have i₂ := eq1465
       grind)
    | exact superpose eq1465 eq332477
    | exact resolve eq332477 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq333386 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (k X0 X0))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1466 eq332477
    | exact resolve eq332477 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq334036 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq333386 x
       have i₂ := eq332477 sF3 x sF2
       grind)
    | (have i₁ := eq333386 x
       have i₂ := eq332477 x x (M.op (M.op sF3 sF2) (M.op sF3 (k x x)))
       grind)
    | exact superpose eq332477 eq333386
    | exact resolve eq333386 eq332477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333386
  have eq334037 : x = y ∨ (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq333352 x
       have i₂ := eq332477 y x x
       grind)
    | (have i₁ := eq333352 x
       have i₂ := eq332477 x x (M.op (M.op y x) (M.op y (k x x)))
       grind)
    | exact superpose eq332477 eq333352
    | exact resolve eq333352 eq332477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332477 eq333352
  have eq334294 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq334036
       have i₂ := eq1524 sF3
       grind)
    | exact superpose eq1524 eq334036
    | exact resolve eq334036 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334036
  have eq334295 : (M.op x y) = (k x y) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq334037
       have i₂ := eq1524 y
       grind)
    | exact superpose eq1524 eq334037
    | exact resolve eq334037 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334037
  have eq365600 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq334295
       grind)
    | exact superpose eq334295 eq40
    | exact resolve eq40 eq334295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq334295
  have eq365601 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq365600
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq365600
    | exact resolve eq365600 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365600
  have eq365605 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq365601
    | exact resolve eq365601 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365601
  have eq375777 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ y = (k y y) := by
    first
    | exact superpose eq365605 eq334294
    | exact resolve eq334294 eq365605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334294 eq365605
  have eq375788 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    first
    | (have r₁ := eq375777
       have r₂ := eq27
       grind)
    | exact resolve eq375777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375777
  have eq375800 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    first
    | exact superpose eq375788 eq152
    | exact resolve eq152 eq375788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq376149 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    intro X0
    first
    | exact superpose eq375788 eq14937
    | (have j0 := eq14937 (σ y) X0
       grind)
    | exact resolve eq14937 eq375788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14937 eq375788
  have eq376444 : ∀ X0 : G, (τ (σ y)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq376149 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376149
  have eq376612 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    intro X0
    first
    | exact superpose eq31 eq376444
    | exact resolve eq376444 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376444
  have eq376891 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq375800
    | exact resolve eq375800 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375800
  have eq376892 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq376891
  have eq377006 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq376612 X0
       have j1 := eq14706 X0 y
       grind)
    | (have r₁ := eq376612 y
       have r₂ := eq14706 X0 y
       grind)
    | (have r₁ := eq376612 X0
       have r₂ := eq14706 X0 y
       grind)
    | exact resolve eq376612 eq14706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14706 eq376612
  have eq377749 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (k X0 X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq272589 y X0
       have i₂ := eq376892
       grind)
    | exact superpose eq376892 eq272589
    | exact resolve eq272589 eq376892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272589 eq376892
  have eq377895 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (k X0 X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq377749 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq377749
    | (have j0 := eq377749 X0
       grind)
    | exact resolve eq377749 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377749
  have eq378343 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (k X0 X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq377895
    | (have j0 := eq377895 X0
       grind)
    | exact resolve eq377895 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377895
  have eq378688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq377006 eq378343
    | exact resolve eq378343 eq377006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377006 eq378343
  have eq378912 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq378688
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq378688
    | exact resolve eq378688 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378688
  have eq379057 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq378912
    | exact resolve eq378912 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378912
  have eq379118 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq379057
       have r₂ := eq27
       grind)
    | exact resolve eq379057 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379057
  have eq379143 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq379118 eq31
    | exact resolve eq31 eq379118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq379118
  have eq379297 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq379143
    | exact resolve eq379143 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq379143
  have eq379298 : x = y := by grind
  clear eq379297
  have eq379306 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq379298
       grind)
    | exact superpose eq379298 eq18
    | exact resolve eq18 eq379298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq379307 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq379298
       grind)
    | exact superpose eq379298 eq24
    | exact resolve eq24 eq379298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq379298
  have eq379407 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq379307
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq379307
    | exact resolve eq379307 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379307
  have eq379408 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq379306
       have i₂ := eq1524 x
       grind)
    | exact superpose eq1524 eq379306
    | exact resolve eq379306 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379306
  have eq379423 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq379407 eq26
    | exact resolve eq26 eq379407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq379407
  have eq379597 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq379423
       have i₂ := eq1524 sF2
       grind)
    | exact superpose eq1524 eq379423
    | exact resolve eq379423 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524 eq379423
  have eq384027 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq379408
       grind)
    | exact superpose eq379408 eq39
    | exact resolve eq39 eq379408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq379408
  have eq385134 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq384027
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq384027
    | exact resolve eq384027 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq384027
  have eq385467 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq379597 eq385134
    | exact resolve eq385134 eq379597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379597 eq385134
  have eq385694 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq385467
    | exact resolve eq385467 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq385467
  have eq385840 : False := by grind
  exact eq385840
