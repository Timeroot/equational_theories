import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq1597 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 (k X0 X0)))) = X2 := by
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
  have eq1601 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) := by
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
  have eq1611 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
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
  have eq1614 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (k X1 (k X0 X0)) := by
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
  have eq1619 : ∀ X0 X1 X2 : G, (M.op (k X1 (k X0 X0)) (M.op X2 X1)) = X2 := by
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
  have eq1658 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1611 X0 X1 X2
       have i₂ := eq1614 X0 (M.op X1 (M.op X2 X2))
       grind)
    | exact superpose eq1614 eq1611
    | exact resolve eq1611 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1611
  have eq1678 : ∀ X0 X1 X2 : G, (k (M.op X1 (k X2 X2)) (k X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1658 X0 X1 X2
       have i₂ := eq1524 X2
       grind)
    | exact superpose eq1524 eq1658
    | exact resolve eq1658 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1658
  have eq1772 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 X1
       have i₂ := eq1601 (σ X1) X0
       grind)
    | exact superpose eq1601 eq10
    | exact resolve eq10 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2032 : ∀ X0 X2 : G, (M.op (σ (k X0 X0)) X2) = (k X2 (σ (k X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq929 X0 X0
       have i₂ := eq1772 X0 x
       grind)
    | exact superpose eq1772 eq929
    | exact resolve eq929 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2052 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X1 X2 (M.op X1 (M.op X2 X2))
       have i₂ := eq1772 (M.op X1 (M.op X2 X2)) X0
       grind)
    | exact superpose eq1772 eq175
    | exact resolve eq175 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2062 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X0)) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op X1 X1)
       have i₂ := eq1772 (M.op X1 X1) X0
       grind)
    | exact superpose eq1772 eq16
    | exact resolve eq16 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1772
  have eq2102 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X0)) (M.op X2 (k X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2062 X0 X1 X2
       have i₂ := eq1524 X1
       grind)
    | exact superpose eq1524 eq2062
    | exact resolve eq2062 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062
  have eq2107 : ∀ X0 X1 X2 : G, (M.op X1 (k X2 X2)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2052 X0 X1 X2
       have i₂ := eq1524 X2
       grind)
    | exact superpose eq1524 eq2052
    | exact resolve eq2052 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2160 : ∀ X0 X1 X2 : G, (k (M.op X2 (k X1 X1)) (σ (k X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2102 X0 X1 X2
       have i₂ := eq2032 X0 (M.op X2 (k X1 X1))
       grind)
    | exact superpose eq2032 eq2102
    | exact resolve eq2102 eq2032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2032 eq2102
  have eq5544 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 X3))) X1) X2) := by
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
  have eq5744 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (k (M.op X1 (M.op X2 X3)) (M.op X0 X0)) X1) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5544 X0 X1 X2 X3 X4
       have i₂ := eq929 (M.op X1 (M.op X2 X3)) X0
       grind)
    | exact superpose eq929 eq5544
    | exact resolve eq5544 eq929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq5544
  have eq5871 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (k (M.op X1 (M.op X2 X3)) (k X0 X0)) X1) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5744 X0 X1 X2 X3 X4
       have i₂ := eq1524 X0
       grind)
    | exact superpose eq1524 eq5744
    | exact resolve eq5744 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5744
  have eq5964 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (k (M.op X1 (M.op X2 X3)) (k X0 X0)) X1) X2) = (M.op (k X4 X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5871 X0 X1 X2 X3 X4
       have i₂ := eq1524 X4
       grind)
    | exact superpose eq1524 eq5871
    | exact resolve eq5871 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5871
  have eq14678 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1520 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq14680 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14678 X0 X1
       have i₂ := eq1524 X0
       grind)
    | exact superpose eq1524 eq14678
    | (have j0 := eq14678 X0 X1
       grind)
    | exact resolve eq14678 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14678
  have eq14908 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14680 X1 (τ X0)
       have i₂ := eq391 X0 X0
       grind)
    | exact superpose eq391 eq14680
    | (have j0 := eq14680 X1 (τ X0)
       grind)
    | exact resolve eq14680 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq18205 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ (M.op X0 (k X1 X1))) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq307 (M.op X0 (k X1 X1)) (k X2 X2)
       have i₂ := eq2160 X2 X1 X0
       grind)
    | exact superpose eq2160 eq307
    | exact resolve eq307 eq2160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq2160
  have eq150388 : ∀ X0 X1 X3 : G, (M.op (τ X0) (M.op X3 (τ (M.op X0 (k X1 X1))))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1619 x (τ (M.op X0 (k X1 X1))) X3
       have i₂ := eq18205 X0 X1 x
       grind)
    | exact superpose eq18205 eq1619
    | exact resolve eq1619 eq18205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619 eq18205
  have eq268567 : ∀ X0 X1 : G, (M.op x (M.op X0 (τ (M.op (σ x) (k X1 X1))))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq29 eq150388
    | exact resolve eq150388 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150388
  have eq269857 : ∀ X0 X1 : G, (τ (M.op (σ x) (k X1 X1))) = (M.op x (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq268567 (τ (M.op sF2 (k X1 X1))) X1
       have i₂ := eq1601 X0 (τ (M.op sF2 (k X1 X1)))
       grind)
    | exact superpose eq1601 eq268567
    | exact resolve eq268567 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601 eq268567
  have eq271110 : ∀ X0 X1 : G, (M.op (σ x) (k X1 X1)) = (σ (M.op x (k X0 X0))) := by
    intro X0 X1
    first
    | exact superpose eq269857 eq14
    | exact resolve eq14 eq269857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269857
  have eq272459 : ∀ X0 X2 : G, (σ (M.op x (k X0 X0))) = (M.op (σ x) (σ (k X2 X2))) := by
    intro X0 X2
    first
    | exact superpose eq271110 eq2107
    | exact resolve eq2107 eq271110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2107 eq271110
  have eq329680 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (k X0 (k X3 X3)) X1) X0) = (M.op (k X4 X4) (M.op X1 (k X2 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5964 X3 X1 X0 (M.op X1 (k X2 X2)) X4
       have i₂ := eq1597 X2 X1 X0
       grind)
    | exact superpose eq1597 eq5964
    | exact resolve eq5964 eq1597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1597 eq5964
  have eq331165 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (k X0 (k X3 X3)) X1) X0) = (k (M.op X1 (k X2 X2)) (k X4 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq329680 X0 X1 X2 X3 X4
       have i₂ := eq1614 X4 (M.op X1 (k X2 X2))
       grind)
    | exact superpose eq1614 eq329680
    | exact resolve eq329680 eq1614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614 eq329680
  have eq331713 : ∀ X0 X1 X3 : G, (M.op (M.op (k X0 (k X3 X3)) X1) X0) = X1 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq331165 X0 X1 x X3 x
       have i₂ := eq1678 x X1 x
       grind)
    | exact superpose eq1678 eq331165
    | exact resolve eq331165 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331165
  have eq332289 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (k X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq331713 (M.op X0 (k X1 X1)) X3 x
       have i₂ := eq1678 x X0 X1
       grind)
    | exact superpose eq1678 eq331713
    | exact resolve eq331713 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678 eq331713
  have eq333164 : ∀ X0 : G, y = (M.op (M.op y x) (M.op y (k X0 X0))) ∨ (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq332289 y X0 y
       have i₂ := eq1465
       grind)
    | exact superpose eq1465 eq332289
    | exact resolve eq332289 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq333198 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (k X0 X0))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1466 eq332289
    | exact resolve eq332289 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq333847 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq333198 x
       have i₂ := eq332289 sF3 x sF2
       grind)
    | (have i₁ := eq333198 x
       have i₂ := eq332289 x x (M.op (M.op sF3 sF2) (M.op sF3 (k x x)))
       grind)
    | exact superpose eq332289 eq333198
    | exact resolve eq333198 eq332289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333198
  have eq333848 : x = y ∨ (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq333164 x
       have i₂ := eq332289 y x x
       grind)
    | (have i₁ := eq333164 x
       have i₂ := eq332289 x x (M.op (M.op y x) (M.op y (k x x)))
       grind)
    | exact superpose eq332289 eq333164
    | exact resolve eq333164 eq332289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332289 eq333164
  have eq334105 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq333847
       have i₂ := eq1524 sF3
       grind)
    | exact superpose eq1524 eq333847
    | exact resolve eq333847 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333847
  have eq334106 : (M.op x y) = (k x y) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq333848
       have i₂ := eq1524 y
       grind)
    | exact superpose eq1524 eq333848
    | exact resolve eq333848 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333848
  have eq360435 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq334106
       grind)
    | exact superpose eq334106 eq40
    | exact resolve eq40 eq334106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq334106
  have eq360436 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (k y y) := by
    first
    | (have i₁ := eq360435
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq360435
    | exact resolve eq360435 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360435
  have eq360440 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq360436
    | exact resolve eq360436 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360436
  have eq371298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ y = (k y y) := by
    first
    | exact superpose eq360440 eq334105
    | exact resolve eq334105 eq360440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334105 eq360440
  have eq371309 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    first
    | (have r₁ := eq371298
       have r₂ := eq27
       grind)
    | exact resolve eq371298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371298
  have eq371321 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    first
    | exact superpose eq371309 eq152
    | exact resolve eq152 eq371309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq371667 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (τ (σ y)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    intro X0
    first
    | exact superpose eq371309 eq14908
    | (have j0 := eq14908 (σ y) X0
       grind)
    | exact resolve eq14908 eq371309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14908 eq371309
  have eq371954 : ∀ X0 : G, (τ (σ y)) = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    intro X0
    first
    | (have j0 := eq371667 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371667
  have eq372118 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    intro X0
    first
    | exact superpose eq31 eq371954
    | exact resolve eq371954 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371954
  have eq372393 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq371321
    | exact resolve eq371321 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371321
  have eq372394 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq372393
  have eq372508 : ∀ X0 : G, y = (k X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq372118 X0
       have j1 := eq14680 X0 y
       grind)
    | (have r₁ := eq372118 y
       have r₂ := eq14680 X0 y
       grind)
    | (have r₁ := eq372118 X0
       have r₂ := eq14680 X0 y
       grind)
    | exact resolve eq372118 eq14680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14680 eq372118
  have eq373245 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (k X0 X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq272459 y X0
       have i₂ := eq372394
       grind)
    | exact superpose eq372394 eq272459
    | exact resolve eq272459 eq372394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272459 eq372394
  have eq373382 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (k X0 X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq373245 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq373245
    | (have j0 := eq373245 X0
       grind)
    | exact resolve eq373245 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373245
  have eq373826 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ (k X0 X0))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq373382
    | (have j0 := eq373382 X0
       grind)
    | exact resolve eq373382 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373382
  have eq374168 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq372508 eq373826
    | exact resolve eq373826 eq372508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372508 eq373826
  have eq374389 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq374168
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq374168
    | exact resolve eq374168 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374168
  have eq374531 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq374389
    | exact resolve eq374389 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374389
  have eq374589 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq374531
       have r₂ := eq27
       grind)
    | exact resolve eq374531 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374531
  have eq374611 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq374589 eq31
    | exact resolve eq31 eq374589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq374589
  have eq374765 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq374611
    | exact resolve eq374611 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq374611
  have eq374766 : x = y := by grind
  clear eq374765
  have eq374774 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq374766
       grind)
    | exact superpose eq374766 eq18
    | exact resolve eq18 eq374766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq374775 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq374766
       grind)
    | exact superpose eq374766 eq24
    | exact resolve eq24 eq374766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq374766
  have eq374875 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq374775
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq374775
    | exact resolve eq374775 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374775
  have eq374876 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq374774
       have i₂ := eq1524 x
       grind)
    | exact superpose eq1524 eq374774
    | exact resolve eq374774 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374774
  have eq374891 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq374875 eq26
    | exact resolve eq26 eq374875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq374875
  have eq375065 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq374891
       have i₂ := eq1524 sF2
       grind)
    | exact superpose eq1524 eq374891
    | exact resolve eq374891 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524 eq374891
  have eq375087 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq374876
       grind)
    | exact superpose eq374876 eq39
    | exact resolve eq39 eq374876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq374876
  have eq376174 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq375087
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq375087
    | exact resolve eq375087 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq375087
  have eq376499 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq375065 eq376174
    | exact resolve eq376174 eq375065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375065 eq376174
  have eq376719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq376499
    | exact resolve eq376499 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq376499
  have eq376859 : False := by grind
  exact eq376859

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_x_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (k X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq186 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq445 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq323 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq323
    | exact resolve eq323 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq647 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq183 X0 X2 (M.op (M.op X1 X1) (k X2 X2))
       have i₂ := eq16 X0 X1 (k X2 X2)
       grind)
    | exact superpose eq16 eq183
    | exact resolve eq183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq652 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X1 X1) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq647 X0 X1 X2
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq647
    | exact resolve eq647 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq654 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (k X0 X0)) X1) (M.op X2 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 (τ X0) X1 X2
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq186
    | exact resolve eq186 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X1 x x
       have i₂ := eq652 X0 x x
       grind)
    | (have i₁ := eq652 X0 X1 X1
       have i₂ := eq652 (k X1 X1) X1 x
       grind)
    | exact superpose eq652 eq652
    | exact resolve eq652 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq757 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X0 X2
       grind)
    | (have i₁ := eq186 X1 X2 X2
       have i₂ := eq698 X2 X0
       grind)
    | exact superpose eq698 eq186
    | exact resolve eq186 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq698
  have eq773 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) X2) (k X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq757
    | exact resolve eq757 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq1319 : (M.op x y) = (k y x) ∨ (M.op y y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1320 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1320
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq1320
    | exact resolve eq1320 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1323 : (k y y) = (M.op y x) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq1319
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq1319
    | exact resolve eq1319 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq3832 : ∀ X0 X1 X2 : G, (M.op (M.op (τ (k X0 X0)) X1) (k X2 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq773 X2 (τ X0) X1
       have i₂ := eq445 X0 X0
       grind)
    | exact superpose eq445 eq773
    | exact resolve eq773 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq773
  have eq8865 : ∀ X0 : G, (σ y) = (M.op (M.op (τ (k X0 X0)) (σ x)) (k (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1322 eq654
    | exact resolve eq654 eq1322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq8868 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq8865 x
       have i₂ := eq3832 x sF2 sF3
       grind)
    | exact superpose eq3832 eq8865
    | exact resolve eq8865 eq3832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8865
  have eq8869 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq8868
  have eq9233 : ∀ X0 : G, y = (M.op (M.op (τ (k X0 X0)) x) (k y y)) ∨ (M.op x y) = (k y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq654 X0 x y
       have i₂ := eq1323
       grind)
    | exact superpose eq1323 eq654
    | exact resolve eq654 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq1323
  have eq9236 : x = y ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq9233 x
       have i₂ := eq3832 x x y
       grind)
    | exact superpose eq3832 eq9233
    | exact resolve eq9233 eq3832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3832 eq9233
  have eq9237 : (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq9236
  have eq9248 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq9237
       grind)
    | exact superpose eq9237 eq39
    | exact resolve eq39 eq9237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9237
  have eq9249 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq9248
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9248
    | exact resolve eq9248 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9248
  have eq9251 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq9249
    | exact resolve eq9249 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9249
  have eq9254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq9251 eq8869
    | exact resolve eq8869 eq9251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8869 eq9251
  have eq9261 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq9254
       have r₂ := eq27
       grind)
    | exact resolve eq9254 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9254
  have eq9266 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq9261 eq31
    | exact resolve eq31 eq9261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9261
  have eq9291 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq9266
    | exact resolve eq9266 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9266
  have eq9292 : x = y := by grind
  clear eq9291
  have eq9295 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq9292
       grind)
    | exact superpose eq9292 eq18
    | exact resolve eq18 eq9292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq9296 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq9292
       grind)
    | exact superpose eq9292 eq24
    | exact resolve eq24 eq9292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9292
  have eq9309 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq9296
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9296
    | exact resolve eq9296 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9296
  have eq9310 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq9295
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq9295
    | exact resolve eq9295 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9295
  have eq9311 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq9309 eq26
    | exact resolve eq26 eq9309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9309
  have eq9337 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9311
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq9311
    | exact resolve eq9311 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq9311
  have eq9342 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq9310
       grind)
    | exact superpose eq9310 eq39
    | exact resolve eq39 eq9310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq9310
  have eq9511 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9342
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9342
    | exact resolve eq9342 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9342
  have eq9553 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9337 eq9511
    | exact resolve eq9511 eq9337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9337 eq9511
  have eq9581 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9553
    | exact resolve eq9553 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9553
  have eq9599 : False := by grind
  exact eq9599

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then Y else if m(Y,X) = m(Y,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_y_x_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq47 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq14 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq14 X0 X3 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq245 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (σ (k (M.op x y) (k (τ X0) X1))) = (k (σ (M.op x y)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq38 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq38
    | exact resolve eq38 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq349 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq52 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq52 X2 X3 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 X2
       have i₂ := eq349 X0 X2
       grind)
    | (have i₁ := eq14 X2 X1 X2
       have i₂ := eq349 X2 X0
       grind)
    | exact superpose eq349 eq14
    | exact resolve eq14 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X1) X1 X2
       have i₂ := eq349 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq52 (M.op X1 X1) X1 X2
       have i₂ := eq349 (M.op X1 X1) X0
       grind)
    | exact superpose eq349 eq52
    | exact resolve eq52 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq398 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq245 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq245
    | exact resolve eq245 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq412 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21 eq245
    | (have j0 := eq245 X0 (M.op x y)
       grind)
    | exact resolve eq245 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq585 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq52 X2 X3 X0
       grind)
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 X2)) = (M.op (M.op (M.op X3 X3) X0) (M.op (M.op X4 X4) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X4 X4) X2) X3 (M.op X0 X2) X1
       have i₂ := eq14 X0 X4 X2
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X4) = (M.op (M.op (M.op X3 X3) X2) (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 (M.op X4 X4) X3 X2
       have i₂ := eq55 X1 X0 X2 X4
       grind)
    | (have i₁ := eq14 (M.op (M.op X1 X1) (M.op X0 X2)) X1 X0
       have i₂ := eq55 X0 X1 X2 X3
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X2) (M.op (M.op X3 X3) X1)) (M.op X4 (M.op (M.op X0 X0) X1))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X1)) X3 X4
       have i₂ := eq55 (M.op X3 X3) X2 X1 X0
       grind)
    | (have i₁ := eq52 (M.op X3 X3) X1 X2
       have i₂ := eq55 X0 X1 (M.op X1 X1) X3
       grind)
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq832 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op X1 X1) (σ X2)) (M.op (σ X0) (σ X0))) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ X0) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 (σ X2)
       have i₂ := eq85 X2 X0
       grind)
    | (have i₁ := eq14 (σ X1) X1 (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq14
    | (have j1 := eq85 X2 X0
       grind)
    | exact resolve eq14 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq5636 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq352 X1 x X2 x
       have i₂ := eq585 X1 x X2 x X0
       grind)
    | exact superpose eq585 eq352
    | exact resolve eq352 eq585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq6117 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5636 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq352 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq352 eq5636
    | exact resolve eq5636 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq16603 : ∀ X0 X2 : G, (σ X0) = (σ X2) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq832 X0 x X2
       have i₂ := eq365 (σ X0) x (σ X2)
       grind)
    | exact superpose eq365 eq832
    | (have j0 := eq832 X0 x X2
       grind)
    | exact resolve eq832 eq365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq832
  have eq16604 : ∀ X0 X2 : G, (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ X0) = (σ X2) := by
    intro X0 X2
    first
    | (have j0 := eq16603 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16603
  have eq16667 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq16604 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16604
    | (have j0 := eq16604 X0 x
       grind)
    | exact resolve eq16604 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16672 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16604 (τ X0) x
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq16604
    | exact resolve eq16604 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16734 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq16604
    | (have j0 := eq16604 (M.op x y) X0
       grind)
    | exact resolve eq16604 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16743 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op X2 X2) (σ X1)) (σ (k X0 X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X2 (σ X1)
       have i₂ := eq16604 X1 X0
       grind)
    | exact superpose eq16604 eq14
    | (have j1 := eq16604 X0 X1
       grind)
    | exact resolve eq14 eq16604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16604
  have eq16771 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16672 X0 X1
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq16672
    | (have j0 := eq16672 X0 X1
       grind)
    | exact resolve eq16672 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq16672
  have eq16844 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16667 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16667
    | (have j0 := eq16667 y
       grind)
    | exact resolve eq16667 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16667
  have eq16866 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16844
       have i₂ := eq47
       grind)
    | exact superpose eq47 eq16844
    | exact resolve eq16844 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16844
  have eq16879 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq16866
    | exact resolve eq16866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16866
  have eq19207 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16771 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq16771
    | exact resolve eq16771 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16771
  have eq19849 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq47
       have i₂ := eq19207 x y
       grind)
    | exact superpose eq19207 eq47
    | (have j1 := eq19207 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq47 eq19207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq19207
  have eq20035 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq19849
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19849
    | exact resolve eq19849 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19849
  have eq20045 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq20035
    | exact resolve eq20035 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20035
  have eq20062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20045 eq16879
    | exact resolve eq16879 eq20045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16879 eq20045
  have eq20079 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq20062
       have r₂ := eq28
       grind)
    | exact resolve eq20062 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20062
  have eq20105 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq20079 eq30
    | exact resolve eq30 eq20079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20079
  have eq20211 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq20105
    | exact resolve eq20105 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20105
  have eq20212 : x = y := by grind
  clear eq20211
  have eq20239 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq20212
       grind)
    | exact superpose eq20212 eq19
    | exact resolve eq19 eq20212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq20240 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq20212
       grind)
    | exact superpose eq20212 eq25
    | exact resolve eq25 eq20212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq20212
  have eq20346 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq20240
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20240
    | exact resolve eq20240 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq20240
  have eq20373 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20346 eq27
    | exact resolve eq27 eq20346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20346
  have eq20536 : ∀ X0 : G, (M.op x y) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq20239
       have i₂ := eq349 X0 x
       grind)
    | (have i₁ := eq20239
       have i₂ := eq349 x X0
       grind)
    | exact superpose eq349 eq20239
    | exact resolve eq20239 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq20540 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 x X0
       have i₂ := eq20239
       grind)
    | exact superpose eq20239 eq14
    | exact resolve eq14 eq20239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20541 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 (M.op x y)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 x X1
       have i₂ := eq20239
       grind)
    | exact superpose eq20239 eq52
    | exact resolve eq52 eq20239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq20614 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op x y) X0) X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5636 x X0 X1
       have i₂ := eq20239
       grind)
    | exact superpose eq20239 eq5636
    | exact resolve eq5636 eq20239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20615 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6117 X0 x X1
       have i₂ := eq20239
       grind)
    | exact superpose eq20239 eq6117
    | exact resolve eq6117 eq20239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20239
  have eq20829 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20373 eq20536
    | exact resolve eq20536 eq20373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20373
  have eq20875 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op (M.op X3 X3) X1) (M.op (M.op x y) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq589 X1 X0 X2 X3 x
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq589
    | exact resolve eq589 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq20996 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq20536 (M.op X0 X0)
       grind)
    | exact superpose eq20536 eq14
    | exact resolve eq14 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21013 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5636 X0 (M.op X0 X0) X1
       have i₂ := eq20536 (M.op X0 X0)
       grind)
    | exact superpose eq20536 eq5636
    | exact resolve eq5636 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5636
  have eq21031 : ∀ X1 : G, (M.op (M.op (M.op x y) X1) (M.op x y)) = X1 := by
    intro X1
    first
    | (have i₁ := eq21013 x X1
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq21013
    | exact resolve eq21013 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21013
  have eq21046 : ∀ X1 : G, (M.op (M.op x y) (M.op X1 (M.op x y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq20996 x X1
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq20996
    | exact resolve eq20996 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20996
  have eq21144 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 X2)) = (M.op (M.op (M.op x y) X1) (M.op (M.op x y) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20875 X0 X1 X2 x
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq20875
    | exact resolve eq20875 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20875
  have eq21256 : ∀ X1 X2 : G, (M.op (M.op x y) (M.op X1 X2)) = (M.op (M.op (M.op x y) X1) (M.op (M.op x y) X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq21144 x X1 X2
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq21144
    | exact resolve eq21144 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21144
  have eq21323 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq20829 eq28
    | exact resolve eq28 eq20829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq20829
  have eq24890 : ∀ X0 : G, (σ X0) = (M.op (M.op (M.op x y) (σ (M.op x y))) (σ (k X0 (M.op x y)))) ∨ (σ X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq16734 eq20540
    | (have j1 := eq16734 X0
       grind)
    | exact resolve eq20540 eq16734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16734 eq20540
  have eq26999 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op (M.op x y) X1) X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq20614 eq6117
    | exact resolve eq6117 eq20614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6117 eq20614
  have eq27051 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op (M.op x y) X1) X0) (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26999 X0 X1 x
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq26999
    | exact resolve eq26999 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26999
  have eq27353 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op X0 (M.op (M.op X1 X0) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq20615 eq20615
    | exact resolve eq20615 eq20615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20615
  have eq35488 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op (M.op x y) (σ (M.op x y))) (k X0 (σ (M.op x y)))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq24890 (τ X0)
       have i₂ := eq35 X0 sF0
       grind)
    | exact superpose eq35 eq24890
    | (have j0 := eq24890 (τ X0)
       grind)
    | exact resolve eq24890 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq24890
  have eq35553 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op (M.op x y) (σ (M.op x y))) (k X0 (σ (M.op x y)))) ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq35488
    | (have j0 := eq35488 X0
       grind)
    | exact resolve eq35488 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35488
  have eq35580 : ∀ X0 : G, (M.op (M.op (M.op x y) (σ (M.op x y))) (k X0 (σ (M.op x y)))) = X0 ∨ (σ (τ X0)) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq35553 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35553
    | (have j0 := eq35553 X0
       grind)
    | exact resolve eq35553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35553
  have eq35597 : ∀ X0 : G, (M.op (M.op (M.op x y) (σ (M.op x y))) (k X0 (σ (M.op x y)))) = X0 ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq35580 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35580
    | (have j0 := eq35580 X0
       grind)
    | exact resolve eq35580 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35580
  have eq35729 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k X0 (σ (M.op x y))) (M.op X0 (M.op x y))) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq35597 eq27051
    | (have j1 := eq35597 (M.op (k X0 (σ (M.op x y))) (M.op X0 (M.op x y)))
       grind)
    | exact resolve eq27051 eq35597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35597
  have eq35951 : ∀ X0 : G, (M.op (M.op X0 X0) (σ (M.op x y))) = (k (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq35729 eq366
    | (have j1 := eq35729 (M.op x y)
       grind)
    | exact resolve eq366 eq35729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366 eq35729
  have eq36017 : ∀ X0 : G, (M.op (M.op X0 X0) (σ (M.op x y))) = (k (M.op x y) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq35951 X0
       grind)
    | (have r₁ := eq35951 X0
       have r₂ := eq21323
       grind)
    | exact resolve eq35951 eq21323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35951
  have eq36066 : (M.op (M.op x y) (σ (M.op x y))) = (k (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq36017 x
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq36017
    | exact resolve eq36017 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36017
  have eq205584 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op x y) (σ X1)) (σ (k X0 X1))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16743 X0 X1 x
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq16743
    | (have j0 := eq16743 X0 X1 x
       grind)
    | exact resolve eq16743 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16743
  have eq205721 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (M.op x y) (σ (τ X1))) (σ (τ (k X0 X1)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq205584 (τ X0) (τ X1)
       have i₂ := eq398 X1 X0
       grind)
    | exact superpose eq398 eq205584
    | (have j0 := eq205584 (τ X0) (τ X1)
       grind)
    | exact resolve eq205584 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq205584
  have eq206105 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (M.op x y) (σ (τ X1))) (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq205721 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq205721
    | (have j0 := eq205721 X0 X1
       grind)
    | exact resolve eq205721 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205721
  have eq206317 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op (M.op x y) X1) (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq206105 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq206105
    | (have j0 := eq206105 X0 X1
       grind)
    | exact resolve eq206105 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206105
  have eq206516 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) (k X0 X1)) = X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq206317 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq206317
    | (have j0 := eq206317 X0 X1
       grind)
    | exact resolve eq206317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206317
  have eq206706 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op (M.op (M.op x y) X1) (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq206516 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq206516
    | (have j0 := eq206516 X0 X1
       grind)
    | exact resolve eq206516 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206516
  have eq206805 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) (k X0 X1)) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq206706 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq206706
    | (have j0 := eq206706 X0 X1
       grind)
    | exact resolve eq206706 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206706
  have eq207193 : ∀ X0 : G, (τ X0) = (M.op (M.op (M.op x y) (M.op x y)) (τ (k X0 (σ (M.op x y))))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq412 eq206805
    | (have j0 := eq206805 (τ X0) (M.op (M.op (M.op x y) (M.op x y)) (τ (k X0 (σ (M.op x y)))))
       grind)
    | exact resolve eq206805 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207315 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op X0 (M.op x y))) = X1 ∨ X0 = X1 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f207315_11 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op (M.op x y) X1) X0) (M.op x y))) = X1 := by
      intro X0 X1
      grind
    have f207315_12 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X1) (k X0 X1)) = X0 ∨ X0 = X1 := by
      intro X0 X1
      grind
    have f207315_19 : X1 ≠ (M.op (k X0 X1) (M.op X0 (M.op x y))) := by grind
    have f207315_20 : X0 ≠ X1 := by grind
    have f207315_50 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op X0 (M.op x y))) = X1 ∨ X0 = X1 := by
      intro X0 X1
      first
      | (have i₁ := f207315_11 (k X0 X1) X1
         have i₂ := f207315_12 X0 X1
         grind)
      | exact superpose f207315_12 f207315_11
      | (have j1 := f207315_12 (M.op (k X0 X1) (M.op X0 (M.op x y))) X1
         grind)
      | exact resolve f207315_11 f207315_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f207315_158 : X1 ≠ X1 ∨ X0 = X1 := by
      first
      | (have i₁ := f207315_19
         have i₂ := f207315_50 X0 X1
         grind)
      | exact superpose f207315_50 f207315_19
      | (have j1 := f207315_50 X0 X1
         grind)
      | (have r₁ := f207315_19
         have r₂ := f207315_50 X0 X1
         grind)
      | (have r₁ := f207315_19
         have r₂ := f207315_50 X1 (M.op (k X0 X1) (M.op X0 (M.op x y)))
         grind)
      | (have r₁ := f207315_19
         have r₂ := f207315_50 (M.op (k X0 X1) (M.op X0 (M.op x y))) X1
         grind)
      | exact resolve f207315_19 f207315_50
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f207315_162 : X0 = X1 := by grind
    have f207315_164 : False := by
      first
      | (have r₁ := f207315_162
         have r₂ := f207315_20
         grind)
      | exact resolve f207315_162 f207315_20
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f207315_164
  clear eq27051
  have eq207331 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 (M.op (M.op X3 X3) (k X0 (M.op x y))))) = X2 ∨ (M.op x y) = X0 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq206805 eq623
    | (have j1 := eq206805 (M.op (M.op (M.op X1 X1) X0) (M.op X2 (M.op (M.op X3 X3) (k X0 (M.op x y))))) X2
       grind)
    | exact resolve eq623 eq206805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq207363 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) X0) (M.op (M.op x y) X2)) = (M.op (M.op X1 X1) (k X0 X2)) ∨ X0 = X2 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq206805 eq55
    | (have j1 := eq206805 (M.op (M.op (M.op X3 X3) X0) (M.op (M.op x y) X2)) (M.op (M.op X1 X1) (k X0 X2))
       grind)
    | exact resolve eq55 eq206805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq206805
  have eq207490 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X3 X3) X0) (M.op (M.op x y) X2)) = (M.op (M.op x y) (k X0 X2)) ∨ X0 = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq207363 X0 x X2 X3
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq207363
    | (have j0 := eq207363 (M.op (M.op (M.op X3 X3) X0) (M.op (M.op x y) X2)) x (M.op (M.op x y) (k X0 X2)) X3
       grind)
    | exact resolve eq207363 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207363
  have eq207501 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 (M.op (M.op x y) (k X0 (M.op x y))))) = X2 ∨ (M.op x y) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207331 X0 X1 X2 x
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq207331
    | (have j0 := eq207331 X0 X1 X2 x
       grind)
    | exact resolve eq207331 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207331
  have eq207536 : ∀ X0 : G, (τ X0) = (M.op (M.op x y) (τ (k X0 (σ (M.op x y))))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq207193 X0
       have i₂ := eq20536 sF0
       grind)
    | exact superpose eq20536 eq207193
    | (have j0 := eq207193 X0
       grind)
    | exact resolve eq207193 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207193
  have eq207579 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X2)) = (M.op (M.op x y) (k X0 X2)) ∨ X0 = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq207490 X0 X2 x
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq207490
    | (have j0 := eq207490 (M.op (M.op (M.op x y) X0) (M.op (M.op x y) X2)) (M.op (M.op x y) (k X0 X2)) x
       grind)
    | exact resolve eq207490 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207490
  have eq207583 : ∀ X0 X2 : G, (M.op (M.op (M.op x y) X0) (M.op X2 (M.op (M.op x y) (k X0 (M.op x y))))) = X2 ∨ (M.op x y) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq207501 X0 x X2
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq207501
    | (have j0 := eq207501 X0 x X2
       grind)
    | exact resolve eq207501 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207501
  have eq207639 : ∀ X0 X2 : G, (M.op (M.op x y) (M.op X0 X2)) = (M.op (M.op x y) (k X0 X2)) ∨ X0 = X2 := by
    intro X0 X2
    first
    | exact superpose eq21256 eq207579
    | (have j0 := eq207579 (M.op (M.op x y) (M.op X0 X2)) (M.op (M.op x y) (k X0 X2))
       grind)
    | exact resolve eq207579 eq21256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207579
  have eq216676 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X1 X1) (τ (k X0 (σ (M.op x y))))) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq207536 eq14
    | (have j1 := eq207536 X0
       grind)
    | exact resolve eq14 eq207536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207536
  have eq216721 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x y) (τ (k X0 (σ (M.op x y))))) (τ X0)) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq216676 X0 x
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq216676
    | (have j0 := eq216676 X0 x
       grind)
    | exact resolve eq216676 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216676
  have eq220955 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (k X0 X1) (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op x y))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq207639 eq27353
    | (have j1 := eq207639 (M.op (M.op x y) (M.op x y)) (M.op (k X0 X1) (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op x y)))
       grind)
    | exact resolve eq27353 eq207639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27353 eq207639
  have eq221040 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (k X0 X1) (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq220955 X0 X1
       have i₂ := eq21031 (M.op (M.op sF0 (M.op X0 X1)) sF0)
       grind)
    | exact superpose eq21031 eq220955
    | (have j0 := eq220955 (M.op (M.op x y) (M.op x y)) (M.op (k X0 X1) (M.op X0 X1))
       grind)
    | exact resolve eq220955 eq21031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220955
  have eq221123 : ∀ X0 X1 : G, (M.op x y) = (M.op (k X0 X1) (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq221040 X0 X1
       have i₂ := eq20536 sF0
       grind)
    | exact superpose eq20536 eq221040
    | (have j0 := eq221040 (M.op x y) (M.op (k X0 X1) (M.op X0 X1))
       grind)
    | exact resolve eq221040 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221040
  have eq253000 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X1) (τ X2)) (M.op (M.op (M.op X3 X3) (M.op x y)) (M.op (M.op x y) (τ (k X2 (σ (M.op x y))))))) ∨ (M.op x y) = (τ X2) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq216721 eq615
    | (have j1 := eq216721 X2
       grind)
    | exact resolve eq615 eq216721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq216721
  have eq253038 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X1) (τ X2)) (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (τ (k X2 (σ (M.op x y))))))) ∨ (M.op x y) = (τ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq253000 X0 X1 X2 x
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq253000
    | (have j0 := eq253000 X0 X1 X2 x
       grind)
    | exact resolve eq253000 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253000
  have eq253114 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X1) (τ X2)) (M.op (M.op x y) (M.op (M.op x y) (τ (k X2 (σ (M.op x y))))))) ∨ (M.op x y) = (τ X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq21256 eq253038
    | (have j0 := eq253038 X0 X1 X2
       grind)
    | exact resolve eq253038 eq21256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253038
  have eq253179 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (τ X2)) (M.op (M.op x y) (M.op (M.op x y) (τ (k X2 (σ (M.op x y))))))) ∨ (M.op x y) = (τ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq253114 X0 x X2
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq253114
    | (have j0 := eq253114 X0 x X2
       grind)
    | exact resolve eq253114 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253114
  have eq253234 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op (M.op x y) (M.op (τ X2) (M.op (M.op x y) (τ (k X2 (σ (M.op x y))))))) ∨ (M.op x y) = (τ X2) := by
    intro X0 X2
    first
    | exact superpose eq21256 eq253179
    | (have j0 := eq253179 X0 X2
       grind)
    | exact resolve eq253179 eq21256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21256 eq253179
  have eq253269 : ∀ X2 : G, (M.op x y) = (M.op (M.op x y) (M.op (τ X2) (M.op (M.op x y) (τ (k X2 (σ (M.op x y))))))) ∨ (M.op x y) = (τ X2) := by
    intro X2
    first
    | (have i₁ := eq253234 x X2
       have i₂ := eq20536 x
       grind)
    | exact superpose eq20536 eq253234
    | (have j0 := eq253234 x X2
       grind)
    | exact resolve eq253234 eq20536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20536 eq253234
  have eq265792 : ∀ X0 : G, (k (M.op x y) (k X0 (M.op x y))) = (M.op (M.op (M.op x y) X0) (M.op x y)) ∨ (M.op x y) = X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq207583 X0 (k sF0 (k X0 sF0))
       have i₂ := eq221123 sF0 (k X0 sF0)
       grind)
    | exact superpose eq221123 eq207583
    | (have j0 := eq207583 X0 x
       have j1 := eq221123 (k (M.op x y) (k X0 (M.op x y))) (M.op (M.op (M.op x y) X0) (M.op x y))
       grind)
    | exact resolve eq207583 eq221123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207583 eq221123
  have eq265971 : ∀ X0 : G, (k (M.op x y) (k X0 (M.op x y))) = X0 ∨ (M.op x y) = X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq265792 X0
       have i₂ := eq21031 (M.op (M.op sF0 X0) sF0)
       grind)
    | exact superpose eq21031 eq265792
    | (have j0 := eq265792 X0
       grind)
    | exact resolve eq265792 eq21031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21031 eq265792
  have eq266215 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq265971 eq248
    | (have j1 := eq265971 (τ X0)
       grind)
    | exact resolve eq248 eq265971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq265971
  have eq266331 : ∀ X0 : G, (σ (τ X0)) = (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq266215
    | (have j0 := eq266215 X0
       grind)
    | exact resolve eq266215 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266215
  have eq266341 : ∀ X0 : G, (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 ∨ (τ X0) = (M.op x y) ∨ (M.op x y) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq266331 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq266331
    | (have j0 := eq266331 X0
       grind)
    | exact resolve eq266331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266331
  have eq266349 : ∀ X0 : G, (k (σ (M.op x y)) (k X0 (σ (M.op x y)))) = X0 ∨ (M.op x y) = (τ (k X0 (σ (M.op x y)))) ∨ (τ X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq412 eq266341
    | (have j0 := eq266341 X0
       grind)
    | exact resolve eq266341 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq266341
  have eq711014 : (M.op x y) = (M.op (M.op x y) (M.op (τ (M.op x y)) (M.op (M.op x y) (τ (M.op (M.op x y) (σ (M.op x y))))))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq36066 eq253269
    | (have j0 := eq253269 (M.op x y)
       grind)
    | exact resolve eq253269 eq36066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253269
  have eq836127 : (M.op x y) = (k (σ (M.op x y)) (M.op (M.op x y) (σ (M.op x y)))) ∨ (M.op x y) = (τ (M.op (M.op x y) (σ (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq36066 eq266349
    | (have j0 := eq266349 (M.op (M.op x y) (σ (M.op x y)))
       grind)
    | exact resolve eq266349 eq36066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36066 eq266349
  have eq876156 : (M.op (M.op x y) (σ (M.op x y))) = (M.op (M.op x y) (M.op (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (M.op x y) (σ (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq836127 eq207315
    | (have j0 := eq207315 (M.op (M.op x y) (σ (M.op x y))) (M.op (M.op x y) (M.op (σ (M.op x y)) (M.op x y)))
       grind)
    | exact resolve eq207315 eq836127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207315 eq836127
  have eq876326 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op (M.op x y) (σ (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq876156
       have i₂ := eq21046 (M.op sF0 (M.op sF1 sF0))
       grind)
    | exact superpose eq21046 eq876156
    | exact resolve eq876156 eq21046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21046 eq876156
  have eq876327 : (M.op x y) = (τ (M.op (M.op x y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by grind
  clear eq876326
  have eq877945 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq876327 eq15
    | exact resolve eq15 eq876327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876327
  have eq878306 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq21 eq877945
    | exact resolve eq877945 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877945
  have eq878307 : (σ (M.op x y)) = (M.op (M.op x y) (σ (M.op x y))) ∨ (M.op x y) = (τ (M.op x y)) := by grind
  clear eq878306
  have eq878397 : (M.op x y) = (M.op (M.op x y) (M.op (τ (M.op x y)) (M.op (M.op x y) (τ (σ (M.op x y)))))) ∨ (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq878307 eq711014
    | exact resolve eq711014 eq878307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711014 eq878307
  have eq878614 : (M.op x y) = (M.op (M.op x y) (M.op (τ (M.op x y)) (M.op (M.op x y) (τ (σ (M.op x y)))))) ∨ (M.op x y) = (τ (M.op x y)) := by grind
  clear eq878397
  have eq878743 : (M.op x y) = (M.op (M.op x y) (M.op (τ (M.op x y)) (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq31 eq878614
    | exact resolve eq878614 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq878614
  have eq878864 : (M.op x y) = (τ (M.op x y)) ∨ (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq20541 eq878743
    | exact resolve eq878743 eq20541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20541 eq878743
  have eq878865 : (M.op x y) = (τ (M.op x y)) := by grind
  clear eq878864
  have eq878924 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq878865 eq15
    | exact resolve eq15 eq878865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878865
  have eq879266 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq878924
    | exact resolve eq878924 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq878924
  have eq879285 : False := by grind
  exact eq879285

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,Y) then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyy_pxy_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
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
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq99 (σ X0)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq135 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq135
    | exact resolve eq135 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq210 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq10
    | exact resolve eq10 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq28
    | exact resolve eq28 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq216 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 (M.op X0 X0)
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq31
    | exact resolve eq31 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq256 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq210 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq210
    | exact resolve eq210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq1598 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq213 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq213
    | (have j0 := eq213 y
       grind)
    | exact resolve eq213 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1645 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1598 eq14
    | (have j0 := eq14 (M.op (σ y) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1646 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq1645
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1645
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq1645
    | exact resolve eq1645 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1650 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) := by
    first
    | (have i₁ := eq1646
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1646
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq1646
    | exact resolve eq1646 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1879 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq216
    | (have j0 := eq216 (M.op x y)
       grind)
    | exact resolve eq216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq2261 : (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1879 eq14
    | (have j0 := eq14 (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)
       grind)
    | exact resolve eq14 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq2262 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2261
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2261
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2261
    | exact resolve eq2261 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261
  have eq2266 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq2262
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2262
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2262
    | exact resolve eq2262 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq3392 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1 X0
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X1 X0
       grind)
    | (have r₁ := eq94 x X1 x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3393 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3392 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392
  have eq3398 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq80 eq3393
    | exact resolve eq3393 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3401 : y = (k (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq3393 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3393
    | (have j0 := eq3393 y x
       grind)
    | exact resolve eq3393 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3419 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3401 eq1650
    | exact resolve eq1650 eq3401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650 eq3401
  have eq3422 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3398 eq2266
    | exact resolve eq2266 eq3398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266 eq3398
  have eq3428 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3419
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3419
    | exact resolve eq3419 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq3431 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq3422
    | exact resolve eq3422 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq11385 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3428 eq53
    | exact resolve eq53 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11387 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3428 eq54
    | exact resolve eq54 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428
  have eq11398 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq3431 eq53
    | exact resolve eq53 eq3431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq12508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11398 eq11385
    | exact resolve eq11385 eq11398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11398
  have eq12523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12508
    | exact resolve eq12508 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12508
  have eq12525 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12523
       have r₂ := eq27
       grind)
    | exact resolve eq12523 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12523
  have eq12559 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12525 eq3393
    | exact resolve eq3393 eq12525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12525
  have eq12564 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12559
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq12559
    | exact resolve eq12559 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12559
  have eq12612 : (τ (σ y)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12564 eq256
    | exact resolve eq256 eq12564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq12630 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12564
  have eq12638 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37 eq12612
    | exact resolve eq12612 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12612
  have eq12653 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39 eq12638
    | exact resolve eq12638 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12638
  have eq13416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12653 eq11385
    | exact resolve eq11385 eq12653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11385 eq12653
  have eq13444 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13416
  have eq13459 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq13444
    | exact resolve eq13444 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13444
  have eq13471 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq13459
       have r₂ := eq27
       grind)
    | exact resolve eq13459 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13459
  have eq13482 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13471 eq136
    | exact resolve eq136 eq13471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13471
  have eq13508 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq13482
    | exact resolve eq13482 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13482
  have eq13510 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13508
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13508
    | exact resolve eq13508 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13508
  have eq13589 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13510 eq3431
    | exact resolve eq3431 eq13510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13589
  have eq13636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq13622
    | exact resolve eq13622 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13622
  have eq13646 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13636
       have r₂ := eq27
       grind)
    | exact resolve eq13636 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13636
  have eq13744 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13646 eq3393
    | exact resolve eq3393 eq13646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13646
  have eq13749 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13744
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq13744
    | exact resolve eq13744 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13744
  have eq13766 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13749
       have r₂ := eq12630
       grind)
    | exact resolve eq13749 eq12630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12630 eq13749
  have eq13778 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13766 eq3431
    | exact resolve eq3431 eq13766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13783 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13766 eq13510
    | exact resolve eq13510 eq13766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13510 eq13766
  have eq13813 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13783
  have eq13815 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13778
  have eq13841 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13813 eq26
    | exact resolve eq26 eq13813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13845 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13813 eq39
    | exact resolve eq39 eq13813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13813
  have eq13904 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38 eq13845
    | exact resolve eq13845 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13845
  have eq13913 : y = (τ (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13904 eq39
    | exact resolve eq39 eq13904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13904
  have eq13961 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq13913
    | exact resolve eq13913 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13913
  have eq13969 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq13961 eq38
    | exact resolve eq38 eq13961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13961
  have eq14015 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq13969
    | exact resolve eq13969 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13969
  have eq15093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13841 eq13815
    | exact resolve eq13815 eq13841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13815 eq13841
  have eq15124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15093
  have eq15138 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq15124
       have r₂ := eq27
       grind)
    | exact resolve eq15124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15124
  have eq15147 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15138 eq39
    | exact resolve eq39 eq15138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq15138
  have eq15195 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq15147
    | exact resolve eq15147 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15147
  have eq15203 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15195 eq38
    | exact resolve eq38 eq15195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15195
  have eq15249 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq15203
    | exact resolve eq15203 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15203
  have eq15253 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15249 eq20
    | exact resolve eq20 eq15249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15254 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15249 eq77
    | exact resolve eq77 eq15249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq15280 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq15249
  have eq15281 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15253
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15253
    | exact resolve eq15253 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15253
  have eq15288 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15281 eq42
    | exact resolve eq42 eq15281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq15334 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15288
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq15288
    | exact resolve eq15288 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15288
  have eq17463 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15254 (M.op y x)
       have i₂ := eq15254 x
       grind)
    | exact superpose eq15254 eq15254
    | exact resolve eq15254 eq15254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15254
  have eq17478 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq17463
  have eq17506 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136 y
       have i₂ := eq17478
       grind)
    | exact superpose eq17478 eq136
    | exact resolve eq136 eq17478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17478
  have eq17533 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17506
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17506
    | exact resolve eq17506 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17506
  have eq17559 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15281 eq17533
    | exact resolve eq17533 eq15281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15281
  have eq17614 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq17559
  have eq27962 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14015 eq15334
    | exact resolve eq15334 eq14015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14015 eq15334
  have eq28006 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq27962
  have eq28041 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28006
       have r₂ := eq15280
       grind)
    | exact resolve eq28006 eq15280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15280 eq28006
  have eq28058 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28041
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq28041
    | exact resolve eq28041 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28041
  have eq28066 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28058
       have i₂ := eq136 y
       grind)
    | exact superpose eq136 eq28058
    | exact resolve eq28058 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28058
  have eq28072 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28066
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28066
    | exact resolve eq28066 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28066
  have eq28169 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28072 eq17533
    | exact resolve eq17533 eq28072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17533 eq28072
  have eq28205 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq28169
  have eq28239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28205 eq3431
    | exact resolve eq3431 eq28205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3431 eq28205
  have eq28300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq28239
    | exact resolve eq28239 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28239
  have eq28310 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28300
       have r₂ := eq27
       grind)
    | exact resolve eq28300 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28300
  have eq39619 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28310 eq3393
    | exact resolve eq3393 eq28310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393 eq28310
  have eq39627 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39619
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq39619
    | exact resolve eq39619 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq39619
  have eq42838 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39627 eq17614
    | exact resolve eq17614 eq39627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17614 eq39627
  have eq42911 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq42838
  have eq44508 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42911 eq38
    | exact resolve eq38 eq42911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq42911
  have eq44559 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq44508
    | exact resolve eq44508 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq44508
  have eq44560 : x = (M.op x y) := by grind
  clear eq44559
  have eq44565 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq44560 eq20
    | exact resolve eq20 eq44560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq44574 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq44560 eq80
    | exact resolve eq80 eq44560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq44560
  have eq48431 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44565
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44565
    | exact resolve eq44565 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44565
  have eq48775 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq48431 eq22
    | exact resolve eq22 eq48431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq48776 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq48431 eq26
    | exact resolve eq26 eq48431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq48431
  have eq51632 : x = (M.op x x) := by
    first
    | (have i₁ := eq44574 (M.op x x)
       have i₂ := eq44574 x
       grind)
    | exact superpose eq44574 eq44574
    | exact resolve eq44574 eq44574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44574
  have eq51863 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq136 x
       have i₂ := eq51632
       grind)
    | exact superpose eq51632 eq136
    | exact resolve eq136 eq51632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq51632
  have eq51929 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq51863
       have i₂ := eq48775
       grind)
    | exact superpose eq48775 eq51863
    | exact resolve eq51863 eq48775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48775 eq51863
  have eq51940 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq51929 eq11387
    | (have j0 := eq11387 X0
       grind)
    | exact resolve eq11387 eq51929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11387
  have eq52197 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq51940 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51940
  have eq52313 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq51929 eq54
    | exact resolve eq54 eq51929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq54753 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq52197 eq52313
    | exact resolve eq52313 eq52197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52197 eq52313
  have eq54768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq48776 eq54753
    | exact resolve eq54753 eq48776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54753
  have eq54769 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq54768
       have r₂ := eq27
       grind)
    | exact resolve eq54768 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54768
  have eq56004 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq54769 eq48776
    | exact resolve eq48776 eq54769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48776 eq54769
  have eq56109 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51929 eq56004
    | exact resolve eq56004 eq51929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51929 eq56004
  have eq56641 : False := by grind
  exact eq56641

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyy_pxy_pyx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
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
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq99 (σ X0)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq135 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq135
    | exact resolve eq135 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq210 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq10
    | exact resolve eq10 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq28
    | exact resolve eq28 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq216 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 (M.op X0 X0)
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq31
    | exact resolve eq31 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq256 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq210 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq210
    | exact resolve eq210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq1598 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq213 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq213
    | (have j0 := eq213 y
       grind)
    | exact resolve eq213 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1645 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1598 eq14
    | (have j0 := eq14 (M.op (σ y) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1646 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq1645
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1645
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq1645
    | exact resolve eq1645 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1650 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) := by
    first
    | (have i₁ := eq1646
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1646
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq1646
    | exact resolve eq1646 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1646
  have eq1879 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq216
    | (have j0 := eq216 (M.op x y)
       grind)
    | exact resolve eq216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq2261 : (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1879 eq14
    | (have j0 := eq14 (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)
       grind)
    | exact resolve eq14 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879
  have eq2262 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2261
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2261
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2261
    | exact resolve eq2261 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261
  have eq2266 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq2262
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2262
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2262
    | exact resolve eq2262 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2262
  have eq3392 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1 X0
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X1 X0
       grind)
    | (have r₁ := eq94 x X1 x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3393 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3392 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3392
  have eq3398 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq80 eq3393
    | exact resolve eq3393 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3401 : y = (k (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq3393 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3393
    | (have j0 := eq3393 y x
       grind)
    | exact resolve eq3393 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3419 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3401 eq1650
    | exact resolve eq1650 eq3401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1650 eq3401
  have eq3422 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3398 eq2266
    | exact resolve eq2266 eq3398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266 eq3398
  have eq3428 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3419
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3419
    | exact resolve eq3419 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq3431 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq3422
    | exact resolve eq3422 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq11557 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3428 eq53
    | exact resolve eq53 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11559 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3428 eq54
    | exact resolve eq54 eq3428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428
  have eq11570 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq3431 eq53
    | exact resolve eq53 eq3431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq12823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11570 eq11557
    | exact resolve eq11557 eq11570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11570
  have eq12838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12823
    | exact resolve eq12823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12823
  have eq12840 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12838
       have r₂ := eq27
       grind)
    | exact resolve eq12838 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12838
  have eq12873 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12840 eq3393
    | exact resolve eq3393 eq12840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12840
  have eq12878 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12873
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq12873
    | exact resolve eq12873 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12873
  have eq12926 : (τ (σ y)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12878 eq256
    | exact resolve eq256 eq12878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq12943 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12878
  have eq12951 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37 eq12926
    | exact resolve eq12926 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12926
  have eq12966 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39 eq12951
    | exact resolve eq12951 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12951
  have eq13626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12966 eq11557
    | exact resolve eq11557 eq12966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11557 eq12966
  have eq13653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13626
  have eq13668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq13653
    | exact resolve eq13653 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13653
  have eq13680 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq13668
       have r₂ := eq27
       grind)
    | exact resolve eq13668 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13668
  have eq13691 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13680 eq136
    | exact resolve eq136 eq13680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13680
  have eq13716 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq13691
    | exact resolve eq13691 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13691
  have eq13718 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13716
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13716
    | exact resolve eq13716 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13716
  have eq13796 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13718 eq3431
    | exact resolve eq3431 eq13718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13796
  have eq13842 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq13828
    | exact resolve eq13828 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13828
  have eq13852 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13842
       have r₂ := eq27
       grind)
    | exact resolve eq13842 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13842
  have eq13948 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13852 eq3393
    | exact resolve eq3393 eq13852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13852
  have eq13953 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13948
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq13948
    | exact resolve eq13948 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13948
  have eq13970 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13953
       have r₂ := eq12943
       grind)
    | exact resolve eq13953 eq12943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12943 eq13953
  have eq13982 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13970 eq3431
    | exact resolve eq3431 eq13970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13987 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13970 eq13718
    | exact resolve eq13718 eq13970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13718 eq13970
  have eq14016 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13987
  have eq14018 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13982
  have eq14044 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14016 eq26
    | exact resolve eq26 eq14016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14048 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14016 eq39
    | exact resolve eq39 eq14016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14016
  have eq14107 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38 eq14048
    | exact resolve eq14048 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14048
  have eq14116 : y = (τ (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14107 eq39
    | exact resolve eq39 eq14107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14107
  have eq14164 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq14116
    | exact resolve eq14116 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14116
  have eq14172 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq14164 eq38
    | exact resolve eq38 eq14164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14164
  have eq14218 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq14172
    | exact resolve eq14172 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14172
  have eq15093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14044 eq14018
    | exact resolve eq14018 eq14044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14018 eq14044
  have eq15124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15093
  have eq15138 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq15124
       have r₂ := eq27
       grind)
    | exact resolve eq15124 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15124
  have eq15147 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15138 eq39
    | exact resolve eq39 eq15138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq15138
  have eq15195 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq15147
    | exact resolve eq15147 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15147
  have eq15203 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15195 eq38
    | exact resolve eq38 eq15195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15195
  have eq15249 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq15203
    | exact resolve eq15203 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15203
  have eq15253 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15249 eq20
    | exact resolve eq20 eq15249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15254 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15249 eq77
    | exact resolve eq77 eq15249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq15280 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq15249
  have eq15281 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15253
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15253
    | exact resolve eq15253 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15253
  have eq15288 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15281 eq42
    | exact resolve eq42 eq15281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq15334 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15288
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq15288
    | exact resolve eq15288 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15288
  have eq17463 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15254 (M.op y x)
       have i₂ := eq15254 x
       grind)
    | exact superpose eq15254 eq15254
    | exact resolve eq15254 eq15254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15254
  have eq17478 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq17463
  have eq17506 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136 y
       have i₂ := eq17478
       grind)
    | exact superpose eq17478 eq136
    | exact resolve eq136 eq17478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17478
  have eq17533 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17506
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17506
    | exact resolve eq17506 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17506
  have eq17559 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15281 eq17533
    | exact resolve eq17533 eq15281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15281
  have eq17614 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq17559
  have eq27962 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14218 eq15334
    | exact resolve eq15334 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14218 eq15334
  have eq28006 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq27962
  have eq28041 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28006
       have r₂ := eq15280
       grind)
    | exact resolve eq28006 eq15280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15280 eq28006
  have eq28058 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28041
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq28041
    | exact resolve eq28041 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28041
  have eq28066 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28058
       have i₂ := eq136 y
       grind)
    | exact superpose eq136 eq28058
    | exact resolve eq28058 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28058
  have eq28072 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28066
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28066
    | exact resolve eq28066 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28066
  have eq28169 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28072 eq17533
    | exact resolve eq17533 eq28072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17533 eq28072
  have eq28205 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq28169
  have eq28239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28205 eq3431
    | exact resolve eq3431 eq28205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3431 eq28205
  have eq28300 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq28239
    | exact resolve eq28239 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28239
  have eq28310 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28300
       have r₂ := eq27
       grind)
    | exact resolve eq28300 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28300
  have eq39619 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28310 eq3393
    | exact resolve eq3393 eq28310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393 eq28310
  have eq39627 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39619
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq39619
    | exact resolve eq39619 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq39619
  have eq42838 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39627 eq17614
    | exact resolve eq17614 eq39627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17614 eq39627
  have eq42911 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq42838
  have eq44508 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42911 eq38
    | exact resolve eq38 eq42911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq42911
  have eq44559 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq44508
    | exact resolve eq44508 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq44508
  have eq44560 : x = (M.op x y) := by grind
  clear eq44559
  have eq44565 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq44560 eq20
    | exact resolve eq20 eq44560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq44574 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq44560 eq80
    | exact resolve eq80 eq44560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq44560
  have eq48426 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44565
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44565
    | exact resolve eq44565 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44565
  have eq48770 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq48426 eq22
    | exact resolve eq22 eq48426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq48771 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq48426 eq26
    | exact resolve eq26 eq48426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq48426
  have eq51625 : x = (M.op x x) := by
    first
    | (have i₁ := eq44574 (M.op x x)
       have i₂ := eq44574 x
       grind)
    | exact superpose eq44574 eq44574
    | exact resolve eq44574 eq44574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44574
  have eq51856 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq136 x
       have i₂ := eq51625
       grind)
    | exact superpose eq51625 eq136
    | exact resolve eq136 eq51625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq51625
  have eq51922 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq51856
       have i₂ := eq48770
       grind)
    | exact superpose eq48770 eq51856
    | exact resolve eq51856 eq48770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48770 eq51856
  have eq51933 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq51922 eq11559
    | (have j0 := eq11559 X0
       grind)
    | exact resolve eq11559 eq51922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11559
  have eq52190 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq51933 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51933
  have eq52306 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq51922 eq54
    | exact resolve eq54 eq51922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq54745 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq52190 eq52306
    | exact resolve eq52306 eq52190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52190 eq52306
  have eq54760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq48771 eq54745
    | exact resolve eq54745 eq48771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54745
  have eq54761 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq54760
       have r₂ := eq27
       grind)
    | exact resolve eq54760 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54760
  have eq56000 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq54761 eq48771
    | exact resolve eq48771 eq54761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48771 eq54761
  have eq56105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51922 eq56000
    | exact resolve eq56000 eq51922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51922 eq56000
  have eq56641 : False := by grind
  exact eq56641

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,X) = m(Y,Y) then Y else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyy_pxy_y_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
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
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq99 (σ X0)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq110 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq110
    | exact resolve eq110 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq180 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq10
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq28
    | exact resolve eq28 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq186 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 (M.op X0 X0)
       have i₂ := eq111 X0
       grind)
    | exact superpose eq111 eq31
    | exact resolve eq31 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq224 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq180 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq180
    | exact resolve eq180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1596 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq183 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq183
    | (have j0 := eq183 y
       grind)
    | exact resolve eq183 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq1642 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1596 eq14
    | (have j0 := eq14 (M.op (σ y) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq14 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1645 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq1642
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1642
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq1642
    | exact resolve eq1642 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq1649 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) := by
    first
    | (have i₁ := eq1645
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1645
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq1645
    | exact resolve eq1645 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq1877 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq186
    | (have j0 := eq186 (M.op x y)
       grind)
    | exact resolve eq186 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq2258 : (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1877 eq14
    | (have j0 := eq14 (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)
       grind)
    | exact resolve eq14 eq1877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877
  have eq2261 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq2258
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2258
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2258
    | exact resolve eq2258 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2258
  have eq2265 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq2261
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2261
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2261
    | exact resolve eq2261 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2261
  have eq3390 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1 X0
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X1 X0
       grind)
    | (have r₁ := eq94 x X1 x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3391 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3390 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390
  have eq3396 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq80 eq3391
    | exact resolve eq3391 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3399 : y = (k (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq3391 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3391
    | (have j0 := eq3391 y x
       grind)
    | exact resolve eq3391 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3417 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3399 eq1649
    | exact resolve eq1649 eq3399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649 eq3399
  have eq3420 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3396 eq2265
    | exact resolve eq2265 eq3396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265 eq3396
  have eq3426 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3417
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3417
    | exact resolve eq3417 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3417
  have eq3429 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq3420
    | exact resolve eq3420 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3420
  have eq11383 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3426 eq53
    | exact resolve eq53 eq3426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11385 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3426 eq54
    | exact resolve eq54 eq3426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426
  have eq11396 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq3429 eq53
    | exact resolve eq53 eq3429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq12407 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11396 eq11383
    | exact resolve eq11383 eq11396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11396
  have eq12422 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12407
    | exact resolve eq12407 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12407
  have eq12424 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12422
       have r₂ := eq27
       grind)
    | exact resolve eq12422 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12422
  have eq12458 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12424 eq3391
    | exact resolve eq3391 eq12424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12424
  have eq12463 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq12458
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq12458
    | exact resolve eq12458 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12458
  have eq12513 : (τ (σ y)) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12463 eq224
    | exact resolve eq224 eq12463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq12529 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12463
  have eq12537 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq37 eq12513
    | exact resolve eq12513 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12513
  have eq12552 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq39 eq12537
    | exact resolve eq12537 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12537
  have eq13327 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12552 eq11383
    | exact resolve eq11383 eq12552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11383 eq12552
  have eq13355 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13327
  have eq13370 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq13355
    | exact resolve eq13355 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13355
  have eq13382 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq13370
       have r₂ := eq27
       grind)
    | exact resolve eq13370 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13370
  have eq13395 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13382 eq111
    | exact resolve eq111 eq13382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13382
  have eq13419 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq13395
    | exact resolve eq13395 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13395
  have eq13421 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13419
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13419
    | exact resolve eq13419 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13419
  have eq13500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13421 eq3429
    | exact resolve eq3429 eq13421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13533 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13500
  have eq13547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq13533
    | exact resolve eq13533 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13533
  have eq13557 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13547
       have r₂ := eq27
       grind)
    | exact resolve eq13547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13547
  have eq13655 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13557 eq3391
    | exact resolve eq3391 eq13557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13557
  have eq13660 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13655
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq13655
    | exact resolve eq13655 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13655
  have eq13677 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13660
       have r₂ := eq12529
       grind)
    | exact resolve eq13660 eq12529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12529 eq13660
  have eq13689 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13677 eq3429
    | exact resolve eq3429 eq13677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13694 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13677 eq13421
    | exact resolve eq13421 eq13677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13421 eq13677
  have eq13724 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq13694
  have eq13726 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13689
  have eq13752 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13724 eq26
    | exact resolve eq26 eq13724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13756 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13724 eq39
    | exact resolve eq39 eq13724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13724
  have eq13815 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq38 eq13756
    | exact resolve eq13756 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13756
  have eq13824 : y = (τ (σ (M.op x y))) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13815 eq39
    | exact resolve eq39 eq13815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13815
  have eq13872 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq13824
    | exact resolve eq13824 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13824
  have eq13880 : x = (τ (σ (M.op x y))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq13872 eq38
    | exact resolve eq38 eq13872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13872
  have eq13926 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq13880
    | exact resolve eq13880 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13880
  have eq15091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq13752 eq13726
    | exact resolve eq13726 eq13752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13726 eq13752
  have eq15122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq15091
  have eq15136 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq15122
       have r₂ := eq27
       grind)
    | exact resolve eq15122 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15122
  have eq15145 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15136 eq39
    | exact resolve eq39 eq15136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq15136
  have eq15193 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq15145
    | exact resolve eq15145 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15145
  have eq15201 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15193 eq38
    | exact resolve eq38 eq15193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15193
  have eq15247 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq15201
    | exact resolve eq15201 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15201
  have eq15251 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15247 eq20
    | exact resolve eq20 eq15247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15252 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15247 eq77
    | exact resolve eq77 eq15247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq15278 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq15247
  have eq15279 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15251
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15251
    | exact resolve eq15251 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15251
  have eq15286 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15279 eq42
    | exact resolve eq42 eq15279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq15332 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15286
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq15286
    | exact resolve eq15286 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15286
  have eq17461 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15252 (M.op y x)
       have i₂ := eq15252 x
       grind)
    | exact superpose eq15252 eq15252
    | exact resolve eq15252 eq15252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15252
  have eq17476 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq17461
  have eq17506 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq111 y
       have i₂ := eq17476
       grind)
    | exact superpose eq17476 eq111
    | exact resolve eq111 eq17476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17476
  have eq17531 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17506
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17506
    | exact resolve eq17506 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17506
  have eq17557 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15279 eq17531
    | exact resolve eq17531 eq15279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15279
  have eq17612 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq17557
  have eq27960 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq13926 eq15332
    | exact resolve eq15332 eq13926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13926 eq15332
  have eq28004 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq27960
  have eq28039 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28004
       have r₂ := eq15278
       grind)
    | exact resolve eq28004 eq15278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15278 eq28004
  have eq28056 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28039
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq28039
    | exact resolve eq28039 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28039
  have eq28064 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28056
       have i₂ := eq111 y
       grind)
    | exact superpose eq111 eq28056
    | exact resolve eq28056 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28056
  have eq28070 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28064
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28064
    | exact resolve eq28064 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq28064
  have eq28167 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28070 eq17531
    | exact resolve eq17531 eq28070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17531 eq28070
  have eq28203 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq28167
  have eq28237 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28203 eq3429
    | exact resolve eq3429 eq28203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3429 eq28203
  have eq28298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq28237
    | exact resolve eq28237 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28237
  have eq28308 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq28298
       have r₂ := eq27
       grind)
    | exact resolve eq28298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28298
  have eq39617 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28308 eq3391
    | exact resolve eq3391 eq28308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391 eq28308
  have eq39625 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39617
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq39617
    | exact resolve eq39617 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq39617
  have eq42836 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39625 eq17612
    | exact resolve eq17612 eq39625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17612 eq39625
  have eq42909 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq42836
  have eq44506 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq42909 eq38
    | exact resolve eq38 eq42909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq42909
  have eq44557 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq44506
    | exact resolve eq44506 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq44506
  have eq44558 : x = (M.op x y) := by grind
  clear eq44557
  have eq44563 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq44558 eq20
    | exact resolve eq20 eq44558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq44572 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq44558 eq80
    | exact resolve eq80 eq44558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq44558
  have eq48429 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44563
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44563
    | exact resolve eq44563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44563
  have eq48773 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq48429 eq22
    | exact resolve eq22 eq48429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq48774 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq48429 eq26
    | exact resolve eq26 eq48429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq48429
  have eq51630 : x = (M.op x x) := by
    first
    | (have i₁ := eq44572 (M.op x x)
       have i₂ := eq44572 x
       grind)
    | exact superpose eq44572 eq44572
    | exact resolve eq44572 eq44572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44572
  have eq51863 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq111 x
       have i₂ := eq51630
       grind)
    | exact superpose eq51630 eq111
    | exact resolve eq111 eq51630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq51630
  have eq51927 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq51863
       have i₂ := eq48773
       grind)
    | exact superpose eq48773 eq51863
    | exact resolve eq51863 eq48773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48773 eq51863
  have eq51938 : ∀ X0 : G, (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq51927 eq11385
    | (have j0 := eq11385 X0
       grind)
    | exact resolve eq11385 eq51927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11385
  have eq52195 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X0)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq51938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51938
  have eq52311 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq51927 eq54
    | exact resolve eq54 eq51927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq54750 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq52195 eq52311
    | exact resolve eq52311 eq52195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52195 eq52311
  have eq54765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq48774 eq54750
    | exact resolve eq54750 eq48774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54750
  have eq54766 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq54765
       have r₂ := eq27
       grind)
    | exact resolve eq54765 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54765
  have eq56001 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq54766 eq48774
    | exact resolve eq48774 eq54766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48774 eq54766
  have eq56106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51927 eq56001
    | exact resolve eq56001 eq51927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51927 eq56001
  have eq56638 : False := by grind
  exact eq56638

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,X) = X then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_x_pxy_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq88 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq80 eq53
    | exact resolve eq53 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
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
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq99 (σ X0)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq135 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq135
    | exact resolve eq135 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq210 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq10
    | exact resolve eq10 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 (M.op X0 X0)
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq28
    | exact resolve eq28 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq216 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 (M.op X0 X0)
       have i₂ := eq136 X0
       grind)
    | exact superpose eq136 eq31
    | exact resolve eq31 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq256 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq210 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq210
    | exact resolve eq210 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq373 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = (M.op (M.op X0 X0) X1) ∨ (k (M.op X0 X0) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op x x) X1
       have i₂ := eq53 x x x
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1581 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq213 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq213
    | (have j0 := eq213 y
       grind)
    | exact resolve eq213 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq1620 : (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq1581 eq14
    | (have j0 := eq14 (σ (M.op x y)) (M.op (σ y) (σ y))
       grind)
    | exact resolve eq14 eq1581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1621 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ (k (M.op x y) (M.op y y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1620
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq1620
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq1620
    | exact resolve eq1620 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1620
  have eq1846 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq216
    | (have j0 := eq216 (M.op x y)
       grind)
    | exact resolve eq216 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq2216 : (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq1846 eq14
    | (have j0 := eq14 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq14 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2217 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ (k x (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2216
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq2216
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq2216
    | exact resolve eq2216 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq3319 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1 X0
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X1 X0
       grind)
    | (have r₁ := eq94 x X1 x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3320 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3319 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3319
  have eq3325 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq80 eq3320
    | exact resolve eq3320 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3328 : y = (k (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq3320 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3320
    | (have j0 := eq3320 y x
       grind)
    | exact resolve eq3320 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320
  have eq3346 : (σ y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3328 eq1621
    | exact resolve eq1621 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621
  have eq3347 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3328 eq1581
    | exact resolve eq1581 eq3328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1581 eq3328
  have eq3349 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3325 eq2217
    | exact resolve eq2217 eq3325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq3350 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3325 eq1846
    | exact resolve eq1846 eq3325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq3325
  have eq3352 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq3347
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3347
    | exact resolve eq3347 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3347
  have eq3353 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3346
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3346
    | exact resolve eq3346 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq3355 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq3350
    | exact resolve eq3350 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq3356 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq3349
    | exact resolve eq3349 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349
  have eq11291 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3353 eq53
    | exact resolve eq53 eq3353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3353
  have eq11304 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq3356 eq53
    | exact resolve eq53 eq3356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12534 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq11304 eq11291
    | exact resolve eq11291 eq11304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11304
  have eq12549 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12534
    | exact resolve eq12534 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12534
  have eq12551 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq12549
       have r₂ := eq27
       grind)
    | exact resolve eq12549 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12549
  have eq12569 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12551 eq256
    | exact resolve eq256 eq12551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12571 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (σ x) = (k (σ x) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq12551 eq373
    | (have r₁ := eq373 (σ x) x
       have r₂ := eq12551
       grind)
    | (have r₁ := eq373 (σ (M.op x y)) x
       have r₂ := eq12551
       grind)
    | exact resolve eq373 eq12551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12580 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq12551 eq54
    | exact resolve eq54 eq12551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12551
  have eq12587 : ∀ X0 : G, (σ x) = (k (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq12571 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12571
  have eq12596 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38 eq12569
    | exact resolve eq12569 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12569
  have eq12626 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12596 eq3356
    | exact resolve eq3356 eq12596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12596
  have eq12657 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq12626
  have eq20396 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12657 eq256
    | exact resolve eq256 eq12657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12657
  have eq20429 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq38 eq20396
    | exact resolve eq20396 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20396
  have eq20430 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq20429
  have eq20455 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq20430 eq54
    | exact resolve eq54 eq20430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20430
  have eq60249 : (σ (M.op x y)) = (σ x) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12587 eq3355
    | (have j1 := eq12587 (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq3355 eq12587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355 eq12587
  have eq60348 : (σ (M.op x y)) = (σ x) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq60249
  have eq60381 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq60348
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq60348
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq60348
    | exact resolve eq60348 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60348
  have eq61582 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq60381 eq12580
    | exact resolve eq12580 eq60381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12580 eq60381
  have eq61596 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq61582
  have eq61603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq61596 eq11291
    | exact resolve eq11291 eq61596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11291 eq61596
  have eq61636 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq61603
  have eq61643 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq61636
    | exact resolve eq61636 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61636
  have eq61647 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq61643
       have r₂ := eq27
       grind)
    | exact resolve eq61643 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61643
  have eq61682 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq61647 eq256
    | exact resolve eq256 eq61647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61685 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq61647 eq373
    | (have r₁ := eq373 (σ (M.op x y)) x
       have r₂ := eq61647
       grind)
    | exact resolve eq373 eq61647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61647
  have eq61703 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (M.op X0 X0) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq61685 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61685
  have eq61729 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq37 eq61682
    | exact resolve eq61682 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61682
  have eq61792 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq61729 eq88
    | exact resolve eq88 eq61729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq61729
  have eq89660 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq61703 eq3352
    | (have j1 := eq61703 (M.op (σ y) (σ y))
       grind)
    | exact resolve eq3352 eq61703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61703
  have eq89801 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq89660
  have eq89854 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq89801
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq89801
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq89801
    | exact resolve eq89801 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89801
  have eq89884 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq89854 eq20455
    | exact resolve eq20455 eq89854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20455 eq89854
  have eq89900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq89884
  have eq89905 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq89900
    | exact resolve eq89900 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89900
  have eq89906 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq89905
       have r₂ := eq27
       grind)
    | exact resolve eq89905 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89905
  have eq89950 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq80 x
       have i₂ := eq89906
       grind)
    | exact superpose eq89906 eq80
    | exact resolve eq80 eq89906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89906
  have eq90073 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq89950 eq61792
    | exact resolve eq61792 eq89950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61792 eq89950
  have eq90107 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq90073
  have eq90182 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq90107 eq39
    | exact resolve eq39 eq90107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq90107
  have eq90236 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq90182
    | exact resolve eq90182 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90182
  have eq90244 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq90236 eq38
    | exact resolve eq38 eq90236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90236
  have eq90301 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq90244
    | exact resolve eq90244 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90244
  have eq90302 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq90301
  have eq90306 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq90302 eq20
    | exact resolve eq20 eq90302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90307 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq90302 eq77
    | exact resolve eq77 eq90302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq90308 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq90302 eq80
    | exact resolve eq80 eq90302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90621 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq90624 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90306
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq90306
    | exact resolve eq90306 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90306
  have eq90635 : (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k y (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq90624 eq42
    | exact resolve eq42 eq90624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq90624
  have eq90687 : (σ (k y (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90635
       have i₂ := eq99 sF1
       grind)
    | exact superpose eq99 eq90635
    | exact resolve eq90635 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90635
  have eq90734 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90307 (M.op y x)
       have i₂ := eq90307 x
       grind)
    | exact superpose eq90307 eq90307
    | exact resolve eq90307 eq90307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90307
  have eq90749 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq90734
  have eq91916 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq136 y
       have i₂ := eq90749
       grind)
    | exact superpose eq90749 eq136
    | exact resolve eq136 eq90749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90749
  have eq91947 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq91916
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq91916
    | exact resolve eq91916 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91916
  have eq98355 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq90302 eq90687
    | exact resolve eq90687 eq90302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90302 eq90687
  have eq98442 : (σ (k y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq98355
       have r₂ := eq90621
       grind)
    | exact resolve eq98355 eq90621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90621 eq98355
  have eq98459 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98442
       have i₂ := eq99 y
       grind)
    | exact superpose eq99 eq98442
    | exact resolve eq98442 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq98442
  have eq98462 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98459
       have i₂ := eq136 y
       grind)
    | exact superpose eq136 eq98459
    | exact resolve eq98459 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98459
  have eq98463 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98462
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq98462
    | exact resolve eq98462 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq98462
  have eq98545 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98463 eq91947
    | exact resolve eq91947 eq98463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91947 eq98463
  have eq98582 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq98545
  have eq98616 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98582 eq3356
    | exact resolve eq3356 eq98582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3356 eq98582
  have eq98736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq98616
    | exact resolve eq98616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98616
  have eq98746 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq98736
       have r₂ := eq27
       grind)
    | exact resolve eq98736 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98736
  have eq111539 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98746 eq256
    | exact resolve eq256 eq98746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq98746
  have eq111582 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq111539
    | exact resolve eq111539 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111539
  have eq114756 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90308 x
       have i₂ := eq111582
       grind)
    | exact superpose eq111582 eq90308
    | exact resolve eq90308 eq111582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90308 eq111582
  have eq114794 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq114756
  have eq114813 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq114794
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114794
    | exact resolve eq114794 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq114794
  have eq114814 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq114813
  have eq114820 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114814 eq38
    | exact resolve eq38 eq114814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq114814
  have eq114891 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq114820
    | exact resolve eq114820 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq114820
  have eq114892 : x = (M.op x y) := by grind
  clear eq114891
  have eq114897 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq114892 eq20
    | exact resolve eq20 eq114892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq114906 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq114892 eq80
    | exact resolve eq80 eq114892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq114892
  have eq133717 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq114897
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq114897
    | exact resolve eq114897 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114897
  have eq134610 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq133717 eq22
    | exact resolve eq22 eq133717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq134611 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq133717 eq26
    | exact resolve eq26 eq133717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq133717
  have eq143516 : x = (M.op x x) := by
    first
    | (have i₁ := eq114906 (M.op x x)
       have i₂ := eq114906 x
       grind)
    | exact superpose eq114906 eq114906
    | exact resolve eq114906 eq114906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114906
  have eq143769 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq136 x
       have i₂ := eq143516
       grind)
    | exact superpose eq143516 eq136
    | exact resolve eq136 eq143516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq143516
  have eq143827 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq143769
       have i₂ := eq134610
       grind)
    | exact superpose eq134610 eq143769
    | exact resolve eq143769 eq134610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134610 eq143769
  have eq144097 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq143827 eq373
    | (have r₁ := eq373 (σ (M.op x y)) x
       have r₂ := eq143827
       grind)
    | exact resolve eq373 eq143827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq144106 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq143827 eq54
    | exact resolve eq54 eq143827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq144115 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (M.op X0 X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq144097 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144097
  have eq146676 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq144115 eq3352
    | (have j1 := eq144115 (M.op (σ y) (σ y))
       grind)
    | exact resolve eq3352 eq144115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352 eq144115
  have eq146742 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq146676
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq146676
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq146676
    | exact resolve eq146676 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq146676
  have eq146756 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq146742 eq144106
    | exact resolve eq144106 eq146742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144106 eq146742
  have eq146771 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq134611 eq146756
    | exact resolve eq146756 eq134611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146756
  have eq146772 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq146771
       have r₂ := eq27
       grind)
    | exact resolve eq146771 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146771
  have eq150494 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq146772 eq134611
    | exact resolve eq134611 eq146772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134611 eq146772
  have eq150672 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq143827 eq150494
    | exact resolve eq150494 eq143827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143827 eq150494
  have eq151141 : False := by grind
  exact eq151141

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(X,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_pyx_pxy_pxx_x_Equation2164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq94 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 X2)) ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X2)) = X0 := by
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
  have eq99 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
       have i₂ := eq99 (σ X0)
       grind)
    | exact superpose eq99 eq15
    | exact resolve eq15 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq139 X0
       have i₂ := eq99 X0
       grind)
    | exact superpose eq99 eq139
    | exact resolve eq139 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq139
  have eq188 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
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
  have eq210 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq214 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
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
  have eq217 : ∀ X0 : G, (σ (k (M.op x y) (M.op X0 X0))) = (k (σ (M.op x y)) (M.op (σ X0) (σ X0))) := by
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
  have eq220 : ∀ X0 : G, (σ (k x (M.op X0 X0))) = (k (σ x) (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq31 (M.op X0 X0)
       have i₂ := eq140 X0
       grind)
    | exact superpose eq140 eq31
    | exact resolve eq31 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq260 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq214 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq214
    | exact resolve eq214 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1612 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq217 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq217
    | (have j0 := eq217 y
       grind)
    | exact resolve eq217 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq1857 : (σ (k x (M.op (M.op x y) (M.op x y)))) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq220
    | (have j0 := eq220 (M.op x y)
       grind)
    | exact resolve eq220 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq3335 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 X1 X0
       have i₂ := eq53 X0 X0 X0
       grind)
    | exact superpose eq53 eq94
    | (have j0 := eq94 X0 X1 X0
       grind)
    | (have r₁ := eq94 x X1 x
       have r₂ := eq53 x x x
       grind)
    | exact resolve eq94 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq3336 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3335 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3335
  have eq3341 : (M.op x y) = (k x (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq80 eq3336
    | exact resolve eq3336 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3344 : y = (k (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq3336 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3336
    | (have j0 := eq3336 y x
       grind)
    | exact resolve eq3336 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq3363 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq3344 eq1612
    | exact resolve eq1612 eq3344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612 eq3344
  have eq3366 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq3341 eq1857
    | exact resolve eq1857 eq3341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1857
  have eq3370 : (σ y) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq3363
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3363
    | exact resolve eq3363 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363
  have eq3373 : (σ (M.op x y)) = (k (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq3366
    | exact resolve eq3366 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366
  have eq3766 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (τ X1)) (M.op X0 X2)) = X0 ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = (M.op (τ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (τ X1) X0 X2
       have i₂ := eq210 X1 X0
       grind)
    | (have i₁ := eq53 X1 (τ X0) x
       have i₂ := eq210 X0 X1
       grind)
    | exact superpose eq210 eq53
    | (have j1 := eq210 X1 X0
       grind)
    | exact resolve eq53 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3833 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 (τ X0)) ∨ (k X0 (σ X1)) = X0 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq271359 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (τ X1) (M.op X0 x)
       have i₂ := eq3766 X0 X1 x
       grind)
    | exact superpose eq3766 eq54
    | (have j1 := eq3766 X0 X1 x
       grind)
    | exact resolve eq54 eq3766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3766
  have eq271366 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (M.op X0 X0) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq271359 X0 X1
       have j1 := eq3833 X1 X0
       grind)
    | (have r₁ := eq271359 X1 X0
       have r₂ := eq3833 X0 X1
       grind)
    | (have r₁ := eq271359 (τ X0) X0
       have r₂ := eq3833 X0 (τ X0)
       grind)
    | exact resolve eq271359 eq3833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833 eq271359
  have eq271394 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X1) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq271366 X1 (σ X0)
       grind)
    | exact superpose eq271366 eq15
    | (have j1 := eq271366 X1 (σ X0)
       grind)
    | exact resolve eq15 eq271366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271468 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq271366 X0 X1
       grind)
    | (have i₁ := eq12 (τ X1) X0
       have i₂ := eq271366 X0 X1
       grind)
    | exact superpose eq271366 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq271366 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) (τ X1)
       have r₂ := eq271366 (τ X1) X1
       grind)
    | (have r₁ := eq12 (τ X1) X0
       have r₂ := eq271366 X0 X1
       grind)
    | exact resolve eq12 eq271366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271366
  have eq271511 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq271468 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271468
  have eq271553 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq271394 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq271394
    | (have j0 := eq271394 X0 X1
       grind)
    | exact resolve eq271394 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271394
  have eq272928 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 (τ X1)
       have i₂ := eq271511 (τ X0) X1
       grind)
    | exact superpose eq271511 eq48
    | (have j1 := eq271511 (τ X0) X1
       grind)
    | exact resolve eq48 eq271511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq271511
  have eq273006 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq272928 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq272928
    | (have j0 := eq272928 X0 X1
       grind)
    | exact resolve eq272928 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272928
  have eq273044 : ∀ X0 X1 : G, (k X1 X0) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq273006 X0 X1
       have i₂ := eq140 (τ X0)
       grind)
    | exact superpose eq140 eq273006
    | (have j0 := eq273006 X0 X1
       grind)
    | exact resolve eq273006 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273006
  have eq273048 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq273044 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq273044
    | (have j0 := eq273044 X0 X1
       grind)
    | exact resolve eq273044 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273044
  have eq273050 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq273048 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq273048
    | (have j0 := eq273048 X0 X1
       grind)
    | exact resolve eq273048 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273048
  have eq273976 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq273050 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273050
  have eq279748 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq271553 X0 X1
       grind)
    | exact superpose eq271553 eq10
    | (have j1 := eq271553 X0 X1
       grind)
    | exact resolve eq10 eq271553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271553
  have eq279801 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq279748 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq279748
    | (have j0 := eq279748 X0 X1
       grind)
    | exact resolve eq279748 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279748
  have eq280043 : (σ (M.op x y)) = (σ y) ∨ (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq3370
       have i₂ := eq279801 sF1 (M.op sF3 sF3)
       grind)
    | exact superpose eq279801 eq3370
    | (have j1 := eq279801 (σ (M.op x y)) (M.op (σ y) (σ y))
       grind)
    | exact resolve eq3370 eq279801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3370
  have eq280044 : (σ (M.op x y)) = (σ x) ∨ (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq3373
       have i₂ := eq279801 sF2 (M.op sF1 sF1)
       grind)
    | exact superpose eq279801 eq3373
    | (have j1 := eq279801 (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq3373 eq279801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373
  have eq280594 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq280044
       have i₂ := eq53 sF1 sF1 sF1
       grind)
    | (have i₁ := eq280044
       have i₂ := eq53 x (M.op (M.op sF1 sF1) (M.op sF1 sF1)) x
       grind)
    | exact superpose eq53 eq280044
    | exact resolve eq280044 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280044
  have eq280595 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq280043
       have i₂ := eq53 sF3 sF3 sF3
       grind)
    | (have i₁ := eq280043
       have i₂ := eq53 x (M.op (M.op sF3 sF3) (M.op sF3 sF3)) x
       grind)
    | exact superpose eq53 eq280043
    | exact resolve eq280043 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq280043
  have eq280699 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq280594 eq54
    | exact resolve eq54 eq280594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280594
  have eq280781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq280595 eq280699
    | exact resolve eq280699 eq280595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280812 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq280781
    | exact resolve eq280781 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280781
  have eq280814 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq280812
       have r₂ := eq27
       grind)
    | exact resolve eq280812 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280812
  have eq280820 : y = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq280814 eq39
    | exact resolve eq39 eq280814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq280814
  have eq281127 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37 eq280820
    | exact resolve eq280820 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280820
  have eq281135 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq281127 eq38
    | exact resolve eq38 eq281127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281127
  have eq281855 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq281135
    | exact resolve eq281135 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281135
  have eq281859 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq281855 eq20
    | exact resolve eq20 eq281855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281860 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq281855 eq77
    | exact resolve eq77 eq281855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282571 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq282580 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq281859
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq281859
    | exact resolve eq281859 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281859
  have eq283575 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq281860 (M.op y x)
       have i₂ := eq281860 x
       grind)
    | exact superpose eq281860 eq281860
    | exact resolve eq281860 eq281860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281860
  have eq283606 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq283575
  have eq283665 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq140 y
       have i₂ := eq283606
       grind)
    | exact superpose eq283606 eq140
    | exact resolve eq140 eq283606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283736 : ∀ X0 : G, y ≠ X0 ∨ y = (k X0 y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq273976 X0 y
       have i₂ := eq283606
       grind)
    | exact superpose eq283606 eq273976
    | (have r₁ := eq273976 y y
       have r₂ := eq283606
       grind)
    | exact resolve eq273976 eq283606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273976 eq283606
  have eq283805 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq283665
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq283665
    | exact resolve eq283665 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283665
  have eq283971 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq282580 eq283805
    | exact resolve eq283805 eq282580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282580 eq283805
  have eq284101 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq283971
  have eq284478 : (τ (σ (M.op x y))) = (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq284101 eq260
    | exact resolve eq260 eq284101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq284101
  have eq284633 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq284478
    | exact resolve eq284478 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284478
  have eq284917 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq284633 eq3341
    | exact resolve eq3341 eq284633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341 eq284633
  have eq285141 : y = (k x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq281855 eq284917
    | exact resolve eq284917 eq281855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281855 eq284917
  have eq285245 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq283736 x
       grind)
    | (have r₁ := eq285141
       have r₂ := eq283736 (k x y)
       grind)
    | (have r₁ := eq285141
       have r₂ := eq283736 x
       grind)
    | exact resolve eq285141 eq283736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283736 eq285141
  have eq285435 : x = y ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq279801 x y
       have i₂ := eq285245
       grind)
    | exact superpose eq285245 eq279801
    | (have j0 := eq279801 x y
       grind)
    | exact resolve eq279801 eq285245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279801 eq285245
  have eq285436 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq285435
       have r₂ := eq282571
       grind)
    | exact resolve eq285435 eq282571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282571 eq285435
  have eq285471 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq285436
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq285436
    | exact resolve eq285436 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq285436
  have eq285625 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77 y
       have i₂ := eq285471
       grind)
    | exact superpose eq285471 eq77
    | exact resolve eq77 eq285471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq285471
  have eq285860 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq285625 eq140
    | exact resolve eq140 eq285625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285625
  have eq286000 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq285860
    | exact resolve eq285860 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285860
  have eq286030 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq286000
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq286000
    | exact resolve eq286000 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq286000
  have eq286701 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq286030 eq280699
    | exact resolve eq280699 eq286030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280699 eq286030
  have eq286878 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq286701
    | exact resolve eq286701 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286701
  have eq286926 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq286878
       have r₂ := eq27
       grind)
    | exact resolve eq286878 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286878
  have eq286950 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq286926 eq38
    | exact resolve eq38 eq286926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq286926
  have eq287677 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq37 eq286950
    | exact resolve eq286950 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq286950
  have eq287678 : x = (M.op x y) := by grind
  clear eq287677
  have eq287683 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq287678 eq20
    | exact resolve eq20 eq287678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq287692 : ∀ X0 : G, x = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | exact superpose eq287678 eq80
    | exact resolve eq80 eq287678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq287678
  have eq308063 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq287683
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq287683
    | exact resolve eq287683 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287683
  have eq308839 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq308063 eq22
    | exact resolve eq22 eq308063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq308840 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq308063 eq26
    | exact resolve eq26 eq308063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq308063
  have eq322459 : x = (M.op x x) := by
    first
    | (have i₁ := eq287692 (M.op x x)
       have i₂ := eq287692 x
       grind)
    | exact superpose eq287692 eq287692
    | exact resolve eq287692 eq287692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287692
  have eq324267 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq140 x
       have i₂ := eq322459
       grind)
    | exact superpose eq322459 eq140
    | exact resolve eq140 eq322459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq322459
  have eq324553 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq324267
       have i₂ := eq308839
       grind)
    | exact superpose eq308839 eq324267
    | exact resolve eq324267 eq308839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308839 eq324267
  have eq327279 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq324553 eq54
    | exact resolve eq54 eq324553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq331631 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq280595 eq327279
    | exact resolve eq327279 eq280595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280595 eq327279
  have eq331656 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq308840 eq331631
    | exact resolve eq331631 eq308840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331631
  have eq331657 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq331656
       have r₂ := eq27
       grind)
    | exact resolve eq331656 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331656
  have eq335925 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq331657 eq308840
    | exact resolve eq308840 eq331657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308840 eq331657
  have eq336923 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq324553 eq335925
    | exact resolve eq335925 eq324553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324553 eq335925
  have eq337385 : False := by grind
  exact eq337385
