import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1027`: `x = x ◇ ((x ◇ (y ◇ x)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pxx_pyx_pxy_Equation1027 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1027 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1027.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 (M.op X0 (M.op x X0)) X2
       have i₂ := eq9 X0 x X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq75 : ∀ X0 : G, (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 (M.op (M.op X0 (M.op x X0)) x)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq12
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq175 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq174 X0 X1
       have i₂ := eq75 (σ X0)
       grind)
    | exact superpose eq75 eq174
    | (have j0 := eq174 X0 X1
       grind)
    | exact resolve eq174 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq210 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175 x y
       grind)
    | exact superpose eq175 eq16
    | (have j1 := eq175 x y
       grind)
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq175 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq625 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq626 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq625
    | (have j0 := eq625 X0 X1
       grind)
    | exact resolve eq625 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq706 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (k X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (τ X1)
       have i₂ := eq626 X0 X1
       grind)
    | exact superpose eq626 eq13
    | (have j0 := eq13 X0 (τ X1)
       have j1 := eq626 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (M.op (τ X1) (τ X1))
       have r₂ := eq626 (M.op (τ X1) (τ X1)) X1
       grind)
    | exact resolve eq13 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq722 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (k X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq706 X0 X1
       grind)
    | (have r₁ := eq706 X0 X1
       have r₂ := eq75 X0
       grind)
    | exact resolve eq706 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq728 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq722 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq722
    | (have j0 := eq722 X0 X1
       grind)
    | exact resolve eq722 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq729 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq728 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq1482 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq221 (τ X0) (τ X1)
       have i₂ := eq36 X1 X0
       grind)
    | exact superpose eq36 eq221
    | (have j0 := eq221 (τ X0) (τ X1)
       grind)
    | exact resolve eq221 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1510 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1482 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1482
    | (have j0 := eq1482 X0 X1
       grind)
    | exact resolve eq1482 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1482
  have eq1522 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1510 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1510
    | (have j0 := eq1510 X0 X1
       grind)
    | exact resolve eq1510 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1533 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1522 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1522
    | (have j0 := eq1522 X0 X1
       grind)
    | exact resolve eq1522 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq1538 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1533 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1533
    | (have j0 := eq1533 X0 X1
       grind)
    | exact resolve eq1533 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1543 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1538 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1538
    | (have j0 := eq1538 X0 X1
       grind)
    | exact resolve eq1538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1548 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1543 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1543
    | (have j0 := eq1543 X0 X1
       grind)
    | exact resolve eq1543 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq4882 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq729 X0 X1
       have j1 := eq85 X0 (τ X1)
       grind)
    | (have r₁ := eq729 X0 X1
       have r₂ := eq85 X0 (τ X1)
       grind)
    | exact resolve eq729 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq729
  have eq4883 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4882 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4882
    | exact resolve eq4882 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4915 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq4882 (τ X0) X1
       grind)
    | exact superpose eq4882 eq17
    | (have j1 := eq4882 (τ X0) X1
       grind)
    | exact resolve eq17 eq4882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4882
  have eq4936 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4915 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4915
    | (have j0 := eq4915 X0 X1
       grind)
    | exact resolve eq4915 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915
  have eq4950 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4883 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4883
    | (have j0 := eq4883 X0 X1
       grind)
    | exact resolve eq4883 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4883
  have eq4957 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq4936 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4936
    | (have j0 := eq4936 X0 X1
       grind)
    | exact resolve eq4936 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4936
  have eq4966 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4957 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4957
    | (have j0 := eq4957 X0 X1
       grind)
    | exact resolve eq4957 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4957
  have eq5105 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq4950 X1 X0
       grind)
    | exact superpose eq4950 eq10
    | (have j1 := eq4950 X1 X0
       grind)
    | exact resolve eq10 eq4950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5163 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5105 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq5105
    | (have j0 := eq5105 X0 X1
       grind)
    | exact resolve eq5105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5105
  have eq5281 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq5163 X0 (σ X1)
       grind)
    | exact superpose eq5163 eq22
    | (have j1 := eq5163 X0 (σ X1)
       grind)
    | exact resolve eq22 eq5163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5163
  have eq5356 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4966 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4966
    | (have j0 := eq4966 X1 (σ X0)
       grind)
    | exact resolve eq4966 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4966
  have eq8934 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5356 X1 (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5356
    | exact resolve eq5356 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5356
  have eq9001 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8934 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq8934
    | (have j0 := eq8934 X0 X1
       grind)
    | exact resolve eq8934 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8934
  have eq9200 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X1)
       have i₂ := eq5281 (σ X0) X1
       grind)
    | exact superpose eq5281 eq31
    | (have j1 := eq5281 (σ X0) X1
       grind)
    | exact resolve eq31 eq5281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5281
  have eq9230 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9200 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq9200
    | (have j0 := eq9200 X0 X1
       grind)
    | exact resolve eq9200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9200
  have eq9249 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9230 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9230
    | (have j0 := eq9230 X0 X1
       grind)
    | exact resolve eq9230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9230
  have eq9252 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9249 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq9249
    | (have j0 := eq9249 X0 X1
       grind)
    | exact resolve eq9249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9249
  have eq9550 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq9252 X0 X1
       grind)
    | exact superpose eq9252 eq11
    | (have j1 := eq9252 X0 X1
       grind)
    | exact resolve eq11 eq9252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9252
  have eq9684 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9550 x y
       grind)
    | exact superpose eq9550 eq16
    | (have j1 := eq9550 x y
       grind)
    | exact resolve eq16 eq9550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9550
  have eq9755 : x = (k x y) := by
    first
    | (have j1 := eq4950 y x
       grind)
    | (have r₁ := eq9684
       have r₂ := eq4950 y x
       grind)
    | exact resolve eq9684 eq4950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4950 eq9684
  have eq9804 : x ≠ x ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1548 x y
       have i₂ := eq9755
       grind)
    | exact superpose eq9755 eq1548
    | (have j0 := eq1548 x y
       grind)
    | (have r₁ := eq1548 x y
       have r₂ := eq9755
       grind)
    | exact resolve eq1548 eq9755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548 eq9755
  have eq9808 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq9804
  have eq9821 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq9808
       grind)
    | exact superpose eq9808 eq24
    | exact resolve eq24 eq9808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10075 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9808
       have i₂ := eq9821
       grind)
    | exact superpose eq9821 eq9808
    | exact resolve eq9808 eq9821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9808 eq9821
  have eq10094 : x = y ∨ x = (M.op x y) := by grind
  clear eq10075
  have eq10104 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10094
       grind)
    | exact superpose eq10094 eq16
    | exact resolve eq16 eq10094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10094
  have eq10118 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10104
       have i₂ := eq75 (σ x)
       grind)
    | exact superpose eq75 eq10104
    | exact resolve eq10104 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10104
  have eq10119 : (σ x) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10118
       have i₂ := eq75 x
       grind)
    | exact superpose eq75 eq10118
    | exact resolve eq10118 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10118
  have eq10120 : x = (M.op x y) := by grind
  clear eq10119
  have eq14725 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq210
       have i₂ := eq9001 x y
       grind)
    | exact superpose eq9001 eq210
    | (have j1 := eq9001 x y
       grind)
    | (have r₁ := eq210
       have r₂ := eq9001 x y
       grind)
    | exact resolve eq210 eq9001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq9001
  have eq14825 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k x y)) := by grind
  clear eq14725
  have eq14839 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq221 x y
       grind)
    | (have r₁ := eq14825
       have r₂ := eq221 x y
       grind)
    | exact resolve eq14825 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq14825
  have eq18112 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq24 (σ y) (σ x)
       have i₂ := eq14839
       grind)
    | exact superpose eq14839 eq24
    | exact resolve eq24 eq14839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq25953 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14839
       have i₂ := eq18112
       grind)
    | exact superpose eq18112 eq14839
    | exact resolve eq14839 eq18112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14839 eq18112
  have eq26003 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq25953
  have eq26300 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26003
       grind)
    | exact superpose eq26003 eq16
    | exact resolve eq16 eq26003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26003
  have eq26381 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26300
       have i₂ := eq10120
       grind)
    | exact superpose eq10120 eq26300
    | exact resolve eq26300 eq10120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26300
  have eq26382 : (σ x) = (σ y) := by grind
  clear eq26381
  have eq26646 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26382
       grind)
    | exact superpose eq26382 eq16
    | exact resolve eq16 eq26382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26382
  have eq26817 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq26646
       have i₂ := eq75 (σ x)
       grind)
    | exact superpose eq75 eq26646
    | exact resolve eq26646 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq26646
  have eq26818 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq26817
       have i₂ := eq10120
       grind)
    | exact superpose eq10120 eq26817
    | exact resolve eq26817 eq10120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10120 eq26817
  have eq26819 : False := by grind
  exact eq26819

/-- `Equation1460`: `x = (x ◇ y) ◇ (y ◇ (z ◇ w))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyy_x_pxy_pyy_pyx_Equation1460 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1460 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1460.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X2 X3))) = X0 := by
    intro X0 X1 X2 X3
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
  have eq51 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x y X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x y X0 X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op x y))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) X2 (M.op x x)
       have i₂ := eq14 X0 X2 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X1)) ≠ X0 ∨ (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X1)) = (k (M.op X1 (M.op X2 X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X1 (M.op X2 X3)) (M.op X0 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X1 (M.op X2 X3)) (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq44
    | exact resolve eq44 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq73 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq50
    | exact resolve eq50 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq73
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq73
    | exact resolve eq73 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq71
    | exact resolve eq71 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq80 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq108 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq109 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq113 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq69 sF3
       grind)
    | exact superpose eq69 eq109
    | exact resolve eq109 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq115 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq69 y
       grind)
    | exact superpose eq69 eq113
    | exact resolve eq113 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq108
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq117
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq117
    | exact resolve eq117 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq123
    | exact resolve eq123 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq125 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq124
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq124
    | exact resolve eq124 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq139 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq69 sF1
       grind)
    | exact superpose eq69 eq141
    | exact resolve eq141 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq146 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq144
       have i₂ := eq69 sF0
       grind)
    | exact superpose eq69 eq144
    | exact resolve eq144 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq148 : (σ (k (M.op x y) (M.op y y))) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq38 (M.op y y)
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq38
    | exact resolve eq38 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq244 : ∀ X0 : G, x = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 x) (M.op x (M.op x x))
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq319 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 (M.op X0 X1) (M.op X1 X2)
       have i₂ := eq56 X2 X0 X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq249 eq56
    | exact resolve eq56 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq330 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq256 eq56
    | exact resolve eq56 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq337 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 y X0 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 y X0 x
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq362 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq263 eq56
    | exact resolve eq56 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X2 (M.op X0 (M.op X1 X3)) X1
       have i₂ := eq57 X1 X0 X3
       grind)
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 (M.op X1 (M.op sF4 x))
       have i₂ := eq57 sF4 X1 x
       grind)
    | exact superpose eq57 eq263
    | exact resolve eq263 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq441 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq69 (τ X0)
       grind)
    | exact superpose eq69 eq35
    | exact resolve eq35 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq445 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq452 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq441 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq441
    | exact resolve eq441 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq454 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq452 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq452
    | exact resolve eq452 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq452
  have eq770 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq80 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq13
    | (have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq80 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq788 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq770 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq792 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq788 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq788
    | (have j0 := eq788 X0 X1
       grind)
    | exact resolve eq788 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq793 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq792 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq857 : ∀ X0 X1 X2 X3 : G, (M.op x y) ≠ (M.op (M.op (M.op y (M.op X0 X1)) (M.op X2 X3)) x) ∨ (M.op (M.op (M.op y (M.op X0 X1)) (M.op X2 X3)) x) = (k (M.op (M.op y (M.op X0 X1)) (M.op X2 X3)) x) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq51 eq68
    | exact resolve eq68 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq68
  have eq1383 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (σ X0) (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq56
    | exact resolve eq56 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1385 : ∀ X0 X1 : G, (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq57 (σ X0) X1 (σ X0)
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq57
    | exact resolve eq57 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1740 : ∀ X0 : G, (k (τ X0) (M.op y y)) = (τ (k X0 (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq445 X0 (M.op y y)
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq445
    | exact resolve eq445 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1742 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq445 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq445
    | exact resolve eq445 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1752 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq445 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq445
    | (have j0 := eq445 X0 x
       grind)
    | exact resolve eq445 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq3187 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X1 (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq392 X1 (σ X0) (σ X0) X2
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq392
    | exact resolve eq392 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq3716 : ∀ X0 X1 : G, (M.op (M.op X1 (σ (M.op (M.op x X0) (M.op x y)))) (σ (M.op x X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1385 (M.op x X0) X1
       have i₂ := eq324 (M.op x X0) X0
       grind)
    | (have i₁ := eq1385 (M.op x y) X1
       have i₂ := eq324 (M.op x y) X1
       grind)
    | exact superpose eq324 eq1385
    | exact resolve eq1385 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1385
  have eq11159 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq793 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq793
    | (have j0 := eq793 X0 X1
       grind)
    | exact resolve eq793 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq793
  have eq11162 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (M.op (M.op (σ y) (σ y)) (σ X0)) ∨ (σ X0) = (σ (M.op (M.op y y) (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq11159 (M.op y y) X0
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq11159
    | (have j0 := eq11159 (M.op y y) X0
       grind)
    | exact resolve eq11159 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11247 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11159 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11159
    | exact resolve eq11159 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11324 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11159 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11159
    | (have j0 := eq11159 X0 y
       grind)
    | exact resolve eq11159 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11325 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq21 eq11159
    | (have j0 := eq11159 X0 (M.op x y)
       grind)
    | exact resolve eq11159 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11361 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X0) (M.op x y))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X1) (σ X0)
       have i₂ := eq11159 X1 X0
       grind)
    | exact superpose eq11159 eq54
    | (have j1 := eq11159 X1 X0
       grind)
    | exact resolve eq54 eq11159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11364 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) = X2 ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 (σ X0) X2 (σ X1)
       have i₂ := eq11159 X1 X0
       grind)
    | exact superpose eq11159 eq56
    | (have j1 := eq11159 X1 X0
       grind)
    | exact resolve eq56 eq11159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11159
  have eq11416 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11247 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq11247
    | (have j0 := eq11247 X0 X1
       grind)
    | exact resolve eq11247 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq11247
  have eq11433 : ∀ X0 : G, (σ X0) = (σ y) ∨ (σ (k X0 (M.op y y))) = (M.op (M.op (σ y) (σ y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11162 X0
       have i₂ := eq56 y y y
       grind)
    | exact superpose eq56 eq11162
    | (have j0 := eq11162 X0
       grind)
    | exact resolve eq11162 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11162
  have eq11468 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (M.op (M.op (σ y) (σ y)) (σ X0)) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq11433 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq11433
    | (have j0 := eq11433 X0
       grind)
    | exact resolve eq11433 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11433
  have eq27019 : (M.op x y) ≠ (M.op y x) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq857 x x (M.op x x) x
       have i₂ := eq56 x y (M.op x x)
       grind)
    | exact superpose eq56 eq857
    | exact resolve eq857 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq45846 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11324 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq11324
    | (have j0 := eq11324 x
       grind)
    | exact resolve eq11324 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11324
  have eq45942 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq45846
       have i₂ := eq108
       grind)
    | exact superpose eq108 eq45846
    | exact resolve eq45846 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45846
  have eq45967 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | exact superpose eq27 eq45942
    | exact resolve eq45942 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45942
  have eq45980 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq45967
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq45967
    | exact resolve eq45967 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45967
  have eq46017 : (σ (k (M.op x y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq11325 (M.op y y)
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq11325
    | (have j0 := eq11325 (M.op y y)
       grind)
    | exact resolve eq11325 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11325
  have eq46208 : (k (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | exact superpose eq148 eq46017
    | exact resolve eq46017 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46017
  have eq46225 : (σ y) = (σ (M.op x y)) ∨ (k (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq46208
       have i₂ := eq56 y y y
       grind)
    | exact superpose eq56 eq46208
    | exact resolve eq46208 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46208
  have eq46237 : (σ (M.op x y)) = (σ y) ∨ (k (σ (M.op x y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ y) (σ y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq46225
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq46225
    | exact resolve eq46225 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46225
  have eq46313 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11416 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq454 X0
       grind)
    | exact superpose eq454 eq11416
    | (have j0 := eq11416 X1 (M.op (τ X0) (τ X0))
       grind)
    | exact resolve eq11416 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46318 : ∀ X0 : G, (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) ∨ (σ (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq146 eq11416
    | (have j0 := eq11416 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq11416 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11416
  have eq46491 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq54 eq46318
    | (have j0 := eq46318 X0
       grind)
    | exact resolve eq46318 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq46318
  have eq46495 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46313 X0 X1
       have i₂ := eq56 (τ X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq56 eq46313
    | (have j0 := eq46313 X0 X1
       grind)
    | exact resolve eq46313 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46313
  have eq46506 : ∀ X0 : G, (k X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq46491
    | (have j0 := eq46491 X0
       grind)
    | exact resolve eq46491 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46491
  have eq46509 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46495 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq46495
    | (have j0 := eq46495 X0 X1
       grind)
    | exact resolve eq46495 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46495
  have eq54815 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k X0 (M.op y y)))) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq11468 eq330
    | (have j1 := eq11468 X0
       grind)
    | exact resolve eq330 eq11468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11468
  have eq113648 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ (τ X1))) (σ (τ (k X0 X1)))) = X2 ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11364 (τ X0) (τ X1) X2
       have i₂ := eq1742 X1 X0
       grind)
    | exact superpose eq1742 eq11364
    | (have j0 := eq11364 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq11364 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11364
  have eq114308 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ (τ X1))) (k X0 X1)) = X2 ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113648 X0 X1 X2
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq113648
    | (have j0 := eq113648 X0 X1 X2
       grind)
    | exact resolve eq113648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113648
  have eq114673 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X2 ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114308 X0 X1 X2
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq114308
    | (have j0 := eq114308 X0 X1 X2
       grind)
    | exact resolve eq114308 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114308
  have eq114870 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op (M.op X2 X1) (k X0 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114673 X0 X1 X2
       have i₂ := eq454 X1
       grind)
    | exact superpose eq454 eq114673
    | (have j0 := eq114673 X0 X1 X2
       grind)
    | exact resolve eq114673 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114673
  have eq114945 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X2 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq114870 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq114870
    | (have j0 := eq114870 X0 X1 X2
       grind)
    | exact resolve eq114870 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114870
  have eq197685 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (M.op (σ (τ X0)) (M.op x y))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11361 (τ X0) (τ X1)
       have i₂ := eq1742 X1 X0
       grind)
    | exact superpose eq1742 eq11361
    | (have j0 := eq11361 (τ X0) (τ X1)
       grind)
    | exact resolve eq11361 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742 eq11361
  have eq198939 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ (k X0 X1))) (M.op X0 (M.op x y))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq197685 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq197685
    | (have j0 := eq197685 X0 X1
       grind)
    | exact resolve eq197685 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197685
  have eq199408 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (k X0 X1) (M.op X0 (M.op x y))) ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq198939 X0 X1
       have i₂ := eq15 (k X0 X1)
       grind)
    | exact superpose eq15 eq198939
    | (have j0 := eq198939 X0 X1
       grind)
    | exact resolve eq198939 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198939
  have eq199802 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op X0 (M.op x y))) = X1 ∨ (σ (τ X0)) = (σ (M.op (τ X1) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq199408 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq199408
    | (have j0 := eq199408 X0 X1
       grind)
    | exact resolve eq199408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199408
  have eq200125 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 X1) ∨ (M.op (k X0 X1) (M.op X0 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq199802 X0 X1
       have i₂ := eq454 X1
       grind)
    | exact superpose eq454 eq199802
    | (have j0 := eq199802 X0 X1
       grind)
    | exact resolve eq199802 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq199802
  have eq200320 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op (k X0 X1) (M.op X0 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq200125 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq200125
    | (have j0 := eq200125 X0 X1
       grind)
    | exact resolve eq200125 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200125
  have eq3404202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq45980 eq125
    | exact resolve eq125 eq45980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq3404631 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq3404202
       have r₂ := eq28
       grind)
    | exact resolve eq3404202 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404202
  have eq3407838 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq3404631 eq74
    | exact resolve eq74 eq3404631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404631
  have eq3408971 : y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq30 eq3407838
    | exact resolve eq3407838 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3407838
  have eq3408972 : (M.op x y) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq3408971
  have eq3409039 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq27019
       have i₂ := eq3408972
       grind)
    | exact superpose eq3408972 eq27019
    | (have r₁ := eq27019
       have r₂ := eq3408972
       grind)
    | exact resolve eq27019 eq3408972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27019 eq3408972
  have eq3409862 : (M.op x y) = (k y x) ∨ y = (M.op x x) := by grind
  clear eq3409039
  have eq3412324 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq3409862
       grind)
    | exact superpose eq3409862 eq108
    | exact resolve eq108 eq3409862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq3409862
  have eq3412815 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq3412324
    | exact resolve eq3412324 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412324
  have eq3461909 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3412815 eq45980
    | exact resolve eq45980 eq3412815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45980 eq3412815
  have eq3462328 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq3461909
       have r₂ := eq28
       grind)
    | exact resolve eq3461909 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3461909
  have eq3472918 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq3462328 eq74
    | exact resolve eq74 eq3462328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq3462328
  have eq3474052 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq3472918
    | exact resolve eq3472918 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472918
  have eq3474053 : y = (M.op x x) := by grind
  clear eq3474052
  have eq3474124 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq3474053
       grind)
    | exact superpose eq3474053 eq75
    | exact resolve eq75 eq3474053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3474315 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq324 X0 x
       have i₂ := eq3474053
       grind)
    | exact superpose eq3474053 eq324
    | exact resolve eq324 eq3474053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq3474321 : x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq337 x
       have i₂ := eq3474053
       grind)
    | exact superpose eq3474053 eq337
    | exact resolve eq337 eq3474053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq3474354 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq1383 x X0
       have i₂ := eq3474053
       grind)
    | exact superpose eq3474053 eq1383
    | exact resolve eq1383 eq3474053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1383
  have eq3474412 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq319 X0 x x X1
       have i₂ := eq3474053
       grind)
    | exact superpose eq3474053 eq319
    | exact resolve eq319 eq3474053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq319
  have eq3475179 : (σ x) = (M.op (σ y) (σ (M.op x x))) := by
    first
    | (have i₁ := eq3474354 x
       have i₂ := eq3187 x (σ y) x
       grind)
    | exact superpose eq3187 eq3474354
    | exact resolve eq3474354 eq3187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3187 eq3474354
  have eq3475267 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3474124
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3474124
    | exact resolve eq3474124 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474124
  have eq3475327 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq3475179
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq3475179
    | exact resolve eq3475179 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq3475179
  have eq3475360 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq362 eq3475327
    | exact resolve eq3475327 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475327
  have eq3475372 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3475360
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3475360
    | exact resolve eq3475360 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475360
  have eq3475374 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3475372
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3475372
    | exact resolve eq3475372 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475372
  have eq3482245 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq3475374 eq330
    | exact resolve eq330 eq3475374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq3475374
  have eq3483224 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq362 eq3482245
    | (have j0 := eq3482245 (σ y)
       grind)
    | exact resolve eq3482245 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362 eq3482245
  have eq3492367 : x = (M.op y y) := by
    first
    | exact superpose eq3474321 eq3474315
    | exact resolve eq3474315 eq3474321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474321
  have eq3496107 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq3492367
       grind)
    | exact superpose eq3492367 eq115
    | exact resolve eq115 eq3492367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3496686 : ∀ X0 : G, y = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0 y y
       have i₂ := eq3492367
       grind)
    | exact superpose eq3492367 eq56
    | exact resolve eq56 eq3492367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq3497912 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3496107
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3496107
    | exact resolve eq3496107 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3496107
  have eq3511335 : (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3497912 eq46237
    | exact resolve eq46237 eq3497912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46237
  have eq3520971 : ∀ X0 : G, (τ (k X0 (M.op (σ y) (σ y)))) = (M.op (M.op y y) (τ X0)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq1740 X0
       have i₂ := eq46509 y (τ X0)
       grind)
    | exact superpose eq46509 eq1740
    | (have j1 := eq46509 (τ (k X0 (M.op (σ y) (σ y)))) (M.op (M.op y y) (τ X0))
       grind)
    | exact resolve eq1740 eq46509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq3521197 : (k (σ (M.op x y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq148
       have i₂ := eq46509 y sF0
       grind)
    | exact superpose eq46509 eq148
    | (have j1 := eq46509 (k (σ (M.op x y)) (M.op (σ y) (σ y))) (σ (M.op (M.op y y) (M.op x y)))
       grind)
    | exact resolve eq148 eq46509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq46509
  have eq3522144 : (k (σ (M.op x y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3474315 eq3521197
    | exact resolve eq3521197 eq3474315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3521197
  have eq3522236 : ∀ X0 : G, (τ (k X0 (M.op (σ y) (σ y)))) = (M.op x (τ X0)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq3520971 X0
       have i₂ := eq3492367
       grind)
    | exact superpose eq3492367 eq3520971
    | (have j0 := eq3520971 X0
       grind)
    | exact resolve eq3520971 eq3492367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3520971
  have eq3522736 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3522144
       have i₂ := eq3492367
       grind)
    | exact superpose eq3492367 eq3522144
    | exact resolve eq3522144 eq3492367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522144
  have eq3522771 : ∀ X0 : G, (τ (k X0 (σ x))) = (M.op x (τ X0)) ∨ (τ X0) = y := by
    intro X0
    first
    | exact superpose eq3497912 eq3522236
    | (have j0 := eq3522236 X0
       grind)
    | exact resolve eq3522236 eq3497912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522236
  have eq3523083 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3497912 eq3522736
    | exact resolve eq3522736 eq3497912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522736
  have eq3523296 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3523083
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3523083
    | exact resolve eq3523083 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3523083
  have eq3523459 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq3523296
    | exact resolve eq3523296 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523296
  have eq3530316 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3511335 eq3523459
    | exact resolve eq3523459 eq3511335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3511335
  have eq3532569 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ (k X0 x))) ∨ (σ X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq54815 X0
       have i₂ := eq3492367
       grind)
    | exact superpose eq3492367 eq54815
    | (have j0 := eq54815 X0
       grind)
    | exact resolve eq54815 eq3492367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54815 eq3492367
  have eq3532856 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq139 eq3532569
    | (have j0 := eq3532569 (M.op x y)
       grind)
    | exact resolve eq3532569 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq3532569
  have eq3534194 : (M.op (σ x) (σ y)) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq21 eq3532856
    | exact resolve eq3532856 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532856
  have eq3567441 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3523459 eq3534194
    | exact resolve eq3534194 eq3523459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523459 eq3534194
  have eq3625005 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op X0 y)) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | exact superpose eq3474315 eq200320
    | (have j0 := eq200320 X0 X1
       grind)
    | exact resolve eq200320 eq3474315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200320
  have eq3628468 : ∀ X0 : G, (M.op (k (M.op (σ x) (σ y)) X0) (σ x)) = X0 ∨ (M.op (σ x) (σ y)) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq397 eq3625005
    | (have j0 := eq3625005 (M.op (σ x) (σ y)) X0
       grind)
    | exact resolve eq3625005 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq3625005
  have eq3720619 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3567441 eq3530316
    | exact resolve eq3530316 eq3567441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3530316 eq3567441
  have eq3721314 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq3720619
  have eq3721883 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3721314
       have r₂ := eq28
       grind)
    | exact resolve eq3721314 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721314
  have eq3722965 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3721883 eq30
    | exact resolve eq30 eq3721883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3721883
  have eq3726770 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq3722965
    | exact resolve eq3722965 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3722965
  have eq3726771 : y = (M.op x y) := by grind
  clear eq3726770
  have eq3727605 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq3726771 eq21
    | exact resolve eq21 eq3726771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq3727621 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq3726771 eq146
    | exact resolve eq146 eq3726771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq3727653 : ∀ X0 : G, x = (M.op y (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq3726771 eq244
    | exact resolve eq244 eq3726771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq3726771
  have eq3729842 : x = (M.op y x) := by
    first
    | (have i₁ := eq3727653 x
       have i₂ := eq3474412 y x
       grind)
    | exact superpose eq3474412 eq3727653
    | exact resolve eq3727653 eq3474412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474412 eq3727653
  have eq3729873 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq3727621
       have i₂ := eq115
       grind)
    | exact superpose eq115 eq3727621
    | exact resolve eq3727621 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq3727621
  have eq3729887 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3727605
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3727605
    | exact resolve eq3727605 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3727605
  have eq3730281 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3497912 eq3729873
    | exact resolve eq3729873 eq3497912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3497912 eq3729873
  have eq3730618 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3729887 eq27
    | exact resolve eq27 eq3729887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq3738386 : ∀ X0 : G, y = (M.op x (k X0 x)) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq114945 X0 x y
       have i₂ := eq3729842
       grind)
    | exact superpose eq3729842 eq114945
    | (have j0 := eq114945 X0 x x
       grind)
    | exact resolve eq114945 eq3729842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114945 eq3729842
  have eq3738393 : ∀ X0 : G, y = (M.op x (k X0 x)) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq3738386 X0
       have i₂ := eq3474053
       grind)
    | exact superpose eq3474053 eq3738386
    | (have j0 := eq3738386 X0
       grind)
    | exact resolve eq3738386 eq3474053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3474053 eq3738386
  have eq3739694 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq3730281 eq46506
    | (have j0 := eq46506 X0
       grind)
    | exact resolve eq46506 eq3730281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46506 eq3730281
  have eq3743671 : ∀ X0 X1 : G, (M.op (M.op X1 (σ (M.op (M.op x X0) y))) (σ (M.op x X0))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq3474315 eq3716
    | exact resolve eq3716 eq3474315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716 eq3474315
  have eq3743697 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ (M.op x (M.op y X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3743671 (M.op y X1) X0
       have i₂ := eq57 y x X1
       grind)
    | exact superpose eq57 eq3743671
    | exact resolve eq3743671 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq3743671
  have eq3745451 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3743697 X0 x
       have i₂ := eq3496686 x
       grind)
    | exact superpose eq3496686 eq3743697
    | exact resolve eq3743697 eq3496686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3496686 eq3743697
  have eq3745870 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3745451 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq3745451
    | (have j0 := eq3745451 X0
       grind)
    | exact resolve eq3745451 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3745451
  have eq3746135 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq3729887 eq3745870
    | exact resolve eq3745870 eq3729887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3745870
  have eq3746344 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq3746135 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq3746135
    | (have j0 := eq3746135 X0
       grind)
    | exact resolve eq3746135 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3746135
  have eq3855971 : ∀ X0 : G, y = (M.op x (τ (k X0 (σ x)))) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq3738393 (τ X0)
       have i₂ := eq1752 X0
       grind)
    | exact superpose eq1752 eq3738393
    | (have j0 := eq3738393 (M.op x (τ (k X0 (σ x))))
       grind)
    | exact resolve eq3738393 eq1752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752 eq3738393
  have eq3887800 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = (k (M.op (σ x) (σ y)) X0) ∨ (M.op (σ x) (σ y)) = (M.op X0 X0) := by
    intro X0
    first
    | exact superpose eq3628468 eq3746344
    | (have j1 := eq3628468 X0
       grind)
    | exact resolve eq3746344 eq3628468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3628468 eq3746344
  have eq3951642 : y = (M.op x (τ (M.op (σ x) (σ (M.op x y))))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3887800 eq3855971
    | (have j0 := eq3855971 (M.op (σ x) (σ y))
       have j1 := eq3887800 (σ x)
       grind)
    | exact resolve eq3855971 eq3887800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3855971 eq3887800
  have eq3952942 : y = (M.op x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3730618 eq3951642
    | exact resolve eq3951642 eq3730618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3730618 eq3951642
  have eq3953463 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3475267 eq3952942
    | exact resolve eq3952942 eq3475267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475267 eq3952942
  have eq3953811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3729887 eq3953463
    | exact resolve eq3953463 eq3729887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953463
  have eq3954060 : y = (M.op x (τ (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq3953811
       have r₂ := eq28
       grind)
    | exact resolve eq3953811 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953811
  have eq4016597 : y = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3954060
       have i₂ := eq3522771 sF4
       grind)
    | exact superpose eq3522771 eq3954060
    | (have j1 := eq3522771 (k (M.op (σ x) (σ y)) (σ x))
       grind)
    | exact resolve eq3954060 eq3522771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522771 eq3954060
  have eq4017393 : y = (τ (k (M.op (σ x) (σ y)) (σ x))) ∨ y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq4016597
  have eq4021761 : y = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3739694 eq4017393
    | (have j1 := eq3739694 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq4017393 eq3739694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3739694 eq4017393
  have eq4022651 : y = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq4021761
       have r₂ := eq28
       grind)
    | exact resolve eq4021761 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021761
  have eq4022779 : y = (τ (M.op (σ x) (σ y))) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3483224 eq4022651
    | exact resolve eq4022651 eq3483224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3483224 eq4022651
  have eq4022780 : y = (τ (M.op (σ x) (σ y))) := by grind
  clear eq4022779
  have eq4022948 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4022780 eq15
    | exact resolve eq15 eq4022780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022780
  have eq4023829 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4022948
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4022948
    | exact resolve eq4022948 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq4022948
  have eq4023989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3729887 eq4023829
    | exact resolve eq4023829 eq3729887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729887 eq4023829
  have eq4024078 : False := by grind
  exact eq4024078

/-- `Equation1481`: `x = (y ◇ x) ◇ (x ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation1481 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1481 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1481.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
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
  have eq560 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k y y) ≠ (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 x y
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : (k y y) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq560
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq560
    | exact resolve eq560 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq1210 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 y x
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1217 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) := by
    first
    | (have i₁ := eq1210
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq1210
    | exact resolve eq1210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq1218 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1217
       have i₂ := eq21 (σ y) (σ x)
       grind)
    | exact superpose eq21 eq1217
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1217
       have r₂ := eq21 (σ y) (σ x)
       grind)
    | (have r₁ := eq1217
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1217
       have r₂ := eq21 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1217 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1217
  have eq1220 : x = y ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1218
  have eq1296 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1220
       grind)
    | exact superpose eq1220 eq9
    | exact resolve eq9 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220
  have eq1297 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1296
  have eq1298 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1297
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1297
    | exact resolve eq1297 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1297
  have eq1299 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1298
  have eq1300 : (k y y) = (k x x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
  clear eq1299
  have eq1378 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1300
       grind)
    | exact superpose eq1300 eq10
    | exact resolve eq10 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1380 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1378
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1378
    | exact resolve eq1378 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1378
  have eq1381 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq1380
  have eq1384 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1381
       grind)
    | exact superpose eq1381 eq22
    | exact resolve eq22 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1431 : (k y y) = (k x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1384
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1384
    | exact resolve eq1384 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1384
  have eq1453 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq564
       have i₂ := eq1431
       grind)
    | exact superpose eq1431 eq564
    | (have r₁ := eq564
       have r₂ := eq1431
       grind)
    | exact resolve eq564 eq1431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq1431
  have eq1456 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1453
  have eq1460 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1456
       have i₂ := eq20 (σ x) (σ y)
       grind)
    | exact superpose eq20 eq1456
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1456
       have r₂ := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1456
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1456
       have r₂ := eq20 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1456 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1456
  have eq1461 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1460
  have eq1462 : x = y ∨ (σ x) = (σ y) ∨ (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) := by grind
  clear eq1461
  have eq1464 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1462
       have r₂ := eq1381
       grind)
    | exact resolve eq1462 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381 eq1462
  have eq1465 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1464
       grind)
    | exact superpose eq1464 eq9
    | exact resolve eq9 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464
  have eq1466 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1465
  have eq1467 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1466
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1466
    | exact resolve eq1466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1466
  have eq1468 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1467
  have eq1469 : (σ x) = (σ y) := by grind
  clear eq1468
  have eq1471 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1469
       grind)
    | exact superpose eq1469 eq15
    | exact resolve eq15 eq1469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469
  have eq1518 : x = y := by
    first
    | (have i₁ := eq1471
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1471
    | exact resolve eq1471 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq1521 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1518
       grind)
    | exact superpose eq1518 eq9
    | exact resolve eq9 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq1522 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1521
  have eq1523 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1522
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1522
    | exact resolve eq1522 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq1524 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1523
  have eq1525 : False := by grind
  exact eq1525

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation1483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq59 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq59 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq238 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq245 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq238 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq238 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | (have r₁ := eq238 X1 X1
       have r₂ := eq61 X1 X1
       grind)
    | exact resolve eq238 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq238
  have eq532 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq245 (σ X1) (σ X0)
       grind)
    | exact superpose eq245 eq15
    | exact resolve eq15 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq245 X1 X0
       grind)
    | exact superpose eq245 eq532
    | exact resolve eq532 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq532
  have eq542 : False := by grind
  exact eq542

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq202 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq209 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       have j1 := eq70 X0 X1
       grind)
    | (have r₁ := eq202 X0 X1
       have r₂ := eq70 X0 X1
       grind)
    | (have r₁ := eq202 X1 X1
       have r₂ := eq70 X1 X1
       grind)
    | exact resolve eq202 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq202
  have eq517 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq209 (σ X1) (σ X0)
       grind)
    | exact superpose eq209 eq15
    | exact resolve eq15 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq520 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq209 X1 X0
       grind)
    | exact superpose eq209 eq517
    | exact resolve eq517 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq517
  have eq524 : False := by grind
  exact eq524

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X2))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq63 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 (M.op X0 X0))) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X0)) X1 (M.op X0 X0)
       have i₂ := eq9 (M.op X0 X0) X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq271 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = X2 ∨ (M.op (M.op X1 X2) (M.op X0 X0)) = X2 ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq14 X2 (M.op X0 X0)
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 (M.op X0 X0)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 : G, X0 = X1 ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq277 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq272
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq272
    | exact resolve eq272 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq278 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       have j1 := eq274 X1 X0
       grind)
    | (have r₁ := eq275 X0 X1
       have r₂ := eq274 X0 X1
       grind)
    | (have r₁ := eq275 X1 X0
       have r₂ := eq274 X0 X1
       grind)
    | (have r₁ := eq275 X0 X1
       have r₂ := eq274 (k X1 X0) X1
       grind)
    | exact resolve eq275 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq280 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq274 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq282 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0 X1
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq9
    | (have j1 := eq280 X0
       grind)
    | exact resolve eq9 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq280 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq280 X0
       grind)
    | exact resolve eq12 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = X2 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X0
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq9
    | (have j1 := eq280 X0
       grind)
    | exact resolve eq9 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq287 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq283 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq289 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq287 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq287
    | exact resolve eq287 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq287 (τ X0)
       grind)
    | exact superpose eq287 eq17
    | (have j1 := eq287 (τ X0)
       grind)
    | exact resolve eq17 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq287
  have eq312 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq306 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq306
    | (have j0 := eq306 X0
       grind)
    | exact resolve eq306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq328 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq312 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq312
    | (have j0 := eq312 X0
       grind)
    | exact resolve eq312 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq371 : ∀ X0 X2 X3 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X0 X2) (M.op X3 X3))) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X2) (M.op x X0) X3
       have i₂ := eq284 X2 x X0
       grind)
    | exact superpose eq284 eq9
    | (have j1 := eq284 X2 x X2
       grind)
    | exact resolve eq9 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq278 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq278
    | (have j0 := eq278 (σ X1) (σ X0)
       grind)
    | exact resolve eq278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq278 (τ X1) X0
       grind)
    | exact superpose eq278 eq18
    | (have j1 := eq278 (τ X1) X0
       grind)
    | exact resolve eq18 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq551 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq328 (σ X0)
       grind)
    | exact superpose eq328 eq28
    | (have j1 := eq328 (σ X0)
       grind)
    | exact resolve eq28 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq567 : ∀ X0 : G, (k X0 X0) = X0 ∨ (k (σ X0) (σ X0)) = (σ (M.op (τ (σ X0)) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq551 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq551
    | (have j0 := eq551 X0
       grind)
    | exact resolve eq551 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq581 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq567 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq567
    | (have j0 := eq567 X0
       grind)
    | exact resolve eq567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq592 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq581 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq581
    | (have j0 := eq581 X0
       grind)
    | exact resolve eq581 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq612 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ X0))) ∨ (σ (k (σ X0) (σ X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq28 X0 (σ X0)
       have i₂ := eq592 (σ X0)
       grind)
    | exact superpose eq592 eq28
    | (have j1 := eq592 (σ X0)
       grind)
    | exact resolve eq28 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq621 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ (k (σ X0) (σ X0))) = (σ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq612 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq612
    | (have j0 := eq612 X0
       grind)
    | exact resolve eq612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq638 : ∀ X0 : G, (σ (M.op (σ X0) (σ X0))) = (σ (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq621 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq621
    | (have j0 := eq621 X0
       grind)
    | exact resolve eq621 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq1068 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (τ (σ (σ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (σ X0) (σ X0))
       have i₂ := eq638 X0
       grind)
    | exact superpose eq638 eq10
    | (have j1 := eq638 X0
       grind)
    | exact resolve eq10 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq1103 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1068 X0
       have i₂ := eq10 (σ (k X0 X0))
       grind)
    | exact superpose eq10 eq1068
    | (have j0 := eq1068 X0
       grind)
    | exact resolve eq1068 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq20955 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq282 X0 (M.op X0 X0)
       have i₂ := eq371 X0 X0 X0
       grind)
    | exact superpose eq371 eq282
    | (have j0 := eq282 X0 x
       have j1 := eq371 X0 X0 x
       grind)
    | exact resolve eq282 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282 eq371
  have eq20978 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq20955 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20955
  have eq21008 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq20978 X0
       grind)
    | exact superpose eq20978 eq9
    | (have j1 := eq20978 X0
       grind)
    | exact resolve eq9 eq20978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20978
  have eq25454 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq277
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq277
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq277 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25455 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq25454
  have eq32325 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X1 X1)) = X0 ∨ (M.op (M.op X3 X0) (M.op X1 X1)) = X0 ∨ (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X0 X1 X2
       have i₂ := eq271 X0 X1 X2
       grind)
    | exact superpose eq271 eq63
    | (have j1 := eq271 X1 X2 X0
       grind)
    | exact resolve eq63 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq271
  have eq38380 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq444 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq444
    | exact resolve eq444 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq38560 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38380 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq38380
    | (have j0 := eq38380 X0 X1
       grind)
    | exact resolve eq38380 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38380
  have eq38667 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq38560 X1 X0
       grind)
    | exact superpose eq38560 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq38560 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq38560 X0 X1
       grind)
    | exact resolve eq12 eq38560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38560
  have eq38808 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38667 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38667
  have eq38985 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq38808 X0 X1
       grind)
    | exact superpose eq38808 eq10
    | (have j1 := eq38808 X0 X1
       grind)
    | exact resolve eq10 eq38808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39080 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq38985 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq38985
    | (have j0 := eq38985 X0 X1
       grind)
    | exact resolve eq38985 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38985
  have eq72657 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq433 X0 X1
       grind)
    | exact superpose eq433 eq10
    | (have j1 := eq433 X0 X1
       grind)
    | exact resolve eq10 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq72731 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq72657 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq72657
    | (have j0 := eq72657 X0 X1
       grind)
    | exact resolve eq72657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72657
  have eq151221 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72731 x y
       grind)
    | exact superpose eq72731 eq16
    | (have j1 := eq72731 x y
       grind)
    | exact resolve eq16 eq72731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151325 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq72731 X0 X1
       grind)
    | exact superpose eq72731 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq72731 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq72731 X0 X0
       grind)
    | exact resolve eq13 eq72731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151379 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq72731 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72731
  have eq151392 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq151325 X0 X1
       have j1 := eq151379 X0 X1
       grind)
    | (have r₁ := eq151325 X0 X1
       have r₂ := eq151379 X0 X1
       grind)
    | exact resolve eq151325 eq151379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151325
  have eq151435 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq151392 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq151392
    | (have j0 := eq151392 X0 X1
       grind)
    | exact resolve eq151392 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151392
  have eq151460 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq151435 X0 X1
       have j1 := eq151379 X0 X1
       grind)
    | (have r₁ := eq151435 X0 X1
       have r₂ := eq151379 X0 X1
       grind)
    | exact resolve eq151435 eq151379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151379 eq151435
  have eq152915 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq151460 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq151460
    | (have j0 := eq151460 (τ X0) (τ X1)
       grind)
    | exact resolve eq151460 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq153168 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq152915 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq152915
    | (have j0 := eq152915 X0 X1
       grind)
    | exact resolve eq152915 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152915
  have eq153229 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq153168 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq153168
    | (have j0 := eq153168 X0 X1
       grind)
    | exact resolve eq153168 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153168
  have eq153273 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq153229 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq153229
    | (have j0 := eq153229 X0 X1
       grind)
    | exact resolve eq153229 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153229
  have eq153294 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq153273 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq153273
    | (have j0 := eq153273 X0 X1
       grind)
    | exact resolve eq153273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153273
  have eq156064 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ y = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq151221
       have i₂ := eq38808 x y
       grind)
    | exact superpose eq38808 eq151221
    | (have j1 := eq38808 x y
       grind)
    | (have r₁ := eq151221
       have r₂ := eq38808 x y
       grind)
    | exact resolve eq151221 eq38808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38808 eq151221
  have eq156065 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ y = (k x y) := by grind
  clear eq156064
  have eq156066 : y = (k x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq156065
  have eq156077 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq151460 x y
       have i₂ := eq156066
       grind)
    | exact superpose eq156066 eq151460
    | (have j0 := eq151460 x y
       grind)
    | exact resolve eq151460 eq156066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156080 : x ≠ y ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq156066
  have eq156082 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq156077
  have eq156083 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (k x y) := by grind
  clear eq156082
  have eq156088 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq156083
       have r₂ := eq156080
       grind)
    | exact resolve eq156083 eq156080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156080 eq156083
  have eq190080 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X2 X2)) = X1 ∨ (M.op X1 (M.op X2 X2)) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32325 X1 X2 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32325
  have eq190081 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = X1 ∨ (M.op X1 (M.op X2 X2)) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq190080 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190080
  have eq190249 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = X2 ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq190081 X0 X1 (M.op X0 X0)
       have i₂ := eq284 X0 X0 X0
       grind)
    | exact superpose eq284 eq190081
    | (have j1 := eq284 X0 X1 X2
       grind)
    | exact resolve eq190081 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq190081
  have eq191130 : ∀ X0 X2 : G, (M.op X0 X2) = X2 ∨ (M.op X2 X2) = (k X2 X2) ∨ (k X0 X2) = (M.op X0 X2) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq21008 X2 (M.op x X0)
       have i₂ := eq190249 X2 x X0
       grind)
    | exact superpose eq190249 eq21008
    | (have j0 := eq21008 X2 x
       have j1 := eq190249 X2 x X2
       grind)
    | exact resolve eq21008 eq190249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21008 eq190249
  have eq191271 : ∀ X0 X2 : G, (M.op X0 X2) = X2 ∨ (M.op X2 X2) = (k X2 X2) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have j0 := eq191130 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191130
  have eq257974 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25455
       have i₂ := eq156088
       grind)
    | exact superpose eq156088 eq25455
    | exact resolve eq25455 eq156088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25455 eq156088
  have eq258030 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq257974
  have eq258047 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq277
       have i₂ := eq258030
       grind)
    | exact superpose eq258030 eq277
    | exact resolve eq277 eq258030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq258049 : x ≠ x ∨ y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq258030
       grind)
    | exact superpose eq258030 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq258030
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq258030
       grind)
    | exact resolve eq12 eq258030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258030
  have eq258135 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq258049
  have eq258136 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq258047
  have eq258158 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq151460 x y
       have i₂ := eq258135
       grind)
    | exact superpose eq258135 eq151460
    | (have j0 := eq151460 x y
       grind)
    | exact resolve eq151460 eq258135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151460 eq258135
  have eq258162 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq258158
  have eq258163 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq258162
  have eq258173 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq258163
       grind)
    | exact superpose eq258163 eq16
    | exact resolve eq16 eq258163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258560 : (σ (M.op x x)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq258173
       have i₂ := eq1103 x
       grind)
    | exact superpose eq1103 eq258173
    | (have j1 := eq1103 x
       grind)
    | exact resolve eq258173 eq1103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq258611 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have j1 := eq592 x
       grind)
    | (have r₁ := eq258560
       have r₂ := eq592 x
       grind)
    | exact resolve eq258560 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592 eq258560
  have eq258622 : (σ (M.op x y)) ≠ (σ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq258611
       grind)
    | exact superpose eq258611 eq16
    | exact resolve eq16 eq258611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258627 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq258611
       grind)
    | exact superpose eq258611 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq258611
       grind)
    | exact resolve eq12 eq258611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258611
  have eq258713 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x x) := by grind
  clear eq258627
  have eq258731 : (σ y) = (σ (k x y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq258713
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq258713
    | exact resolve eq258713 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258713
  have eq258802 : (k x y) = (τ (σ y)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq258731
       grind)
    | exact superpose eq258731 eq10
    | exact resolve eq10 eq258731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258731
  have eq258944 : y = (k x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq258802
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq258802
    | exact resolve eq258802 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258802
  have eq258968 : y ≠ y ∨ x = (M.op x y) ∨ (τ y) = (τ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq153294 x y
       have i₂ := eq258944
       grind)
    | exact superpose eq258944 eq153294
    | (have j0 := eq153294 x y
       grind)
    | (have r₁ := eq153294 x y
       have r₂ := eq258944
       grind)
    | (have r₁ := eq153294 x x
       have r₂ := eq258944
       grind)
    | exact resolve eq153294 eq258944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258969 : x = (M.op x y) ∨ (τ y) = (τ x) ∨ x = (k x x) := by grind
  clear eq258968
  have eq259343 : (σ x) ≠ (σ x) ∨ x = (k x x) ∨ (τ y) = (τ x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq258622
       have i₂ := eq258969
       grind)
    | exact superpose eq258969 eq258622
    | exact resolve eq258622 eq258969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258622 eq258969
  have eq259436 : (σ x) ≠ (σ x) ∨ x = (k x x) ∨ (τ y) = (τ x) := by grind
  clear eq259343
  have eq259437 : (τ y) = (τ x) ∨ x = (k x x) := by grind
  clear eq259436
  have eq259440 : y = (σ (τ x)) ∨ x = (k x x) := by
    first
    | (have i₁ := eq11 y
       have i₂ := eq259437
       grind)
    | exact superpose eq259437 eq11
    | exact resolve eq11 eq259437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259437
  have eq259700 : x = y ∨ x = (k x x) := by
    first
    | (have i₁ := eq259440
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq259440
    | exact resolve eq259440 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259440
  have eq259730 : x = (k x x) ∨ x = (k x x) ∨ x = (k x x) := by
    first
    | (have i₁ := eq258944
       have i₂ := eq259700
       grind)
    | exact superpose eq259700 eq258944
    | exact resolve eq258944 eq259700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258944 eq259700
  have eq259736 : x = (k x x) := by grind
  clear eq259730
  have eq288256 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq258136
       have i₂ := eq258163
       grind)
    | exact superpose eq258163 eq258136
    | exact resolve eq258136 eq258163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258136 eq258163
  have eq288275 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq288256
  have eq288280 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq288275
       have i₂ := eq259736
       grind)
    | exact superpose eq259736 eq288275
    | exact resolve eq288275 eq259736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288275
  have eq288281 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq288280
  have eq288303 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq288281
       grind)
    | exact superpose eq288281 eq16
    | exact resolve eq16 eq288281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288308 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq288281
       grind)
    | exact superpose eq288281 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq288281
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq288281
       grind)
    | exact resolve eq12 eq288281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288395 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq288308
  have eq288425 : (σ y) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq288395
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq288395
    | exact resolve eq288395 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288395
  have eq288547 : (k x y) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq288425
       grind)
    | exact superpose eq288425 eq10
    | exact resolve eq10 eq288425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288425
  have eq288693 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq288547
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq288547
    | exact resolve eq288547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288547
  have eq288752 : y ≠ y ∨ x = (M.op x y) ∨ (τ y) = (τ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153294 x y
       have i₂ := eq288693
       grind)
    | exact superpose eq288693 eq153294
    | (have j0 := eq153294 x y
       grind)
    | (have r₁ := eq153294 x y
       have r₂ := eq288693
       grind)
    | exact resolve eq153294 eq288693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288693
  have eq288753 : x = (M.op x y) ∨ (τ y) = (τ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq288752
  have eq288782 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (τ y) = (τ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq288303
       have i₂ := eq288753
       grind)
    | exact superpose eq288753 eq288303
    | exact resolve eq288303 eq288753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288303 eq288753
  have eq288871 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (τ y) = (τ x) := by grind
  clear eq288782
  have eq288872 : (τ y) = (τ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq288871
  have eq288886 : y = (σ (τ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11 y
       have i₂ := eq288872
       grind)
    | exact superpose eq288872 eq11
    | exact resolve eq11 eq288872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288872
  have eq289166 : x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq288886
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq288886
    | exact resolve eq288886 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288886
  have eq289274 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq288281
       have i₂ := eq289166
       grind)
    | exact superpose eq289166 eq288281
    | exact resolve eq288281 eq289166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288281 eq289166
  have eq289281 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq289274
  have eq289358 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq258173
       have i₂ := eq289281
       grind)
    | exact superpose eq289281 eq258173
    | exact resolve eq258173 eq289281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258173
  have eq292444 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (k x x) ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq289358
       have i₂ := eq191271 x x
       grind)
    | exact superpose eq191271 eq289358
    | (have j1 := eq191271 x x
       grind)
    | exact resolve eq289358 eq191271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292445 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (k x x) := by grind
  clear eq292444
  have eq292446 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (k x x) := by grind
  clear eq292445
  have eq292476 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq292446
       have i₂ := eq259736
       grind)
    | exact superpose eq259736 eq292446
    | exact resolve eq292446 eq259736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292446
  have eq292497 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq292476
       grind)
    | exact superpose eq292476 eq16
    | exact resolve eq16 eq292476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292502 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq292476
       grind)
    | exact superpose eq292476 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq292476
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq292476
       grind)
    | exact resolve eq12 eq292476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292476
  have eq292590 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq292502
  have eq292609 : (σ y) = (σ (k x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq292590
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq292590
    | exact resolve eq292590 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292590
  have eq292742 : (k x y) = (τ (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq292609
       grind)
    | exact superpose eq292609 eq10
    | exact resolve eq10 eq292609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292890 : y = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq292742
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq292742
    | exact resolve eq292742 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292742
  have eq292918 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq292890
       have i₂ := eq278 y x
       grind)
    | exact superpose eq278 eq292890
    | (have j1 := eq278 y x
       grind)
    | exact resolve eq292890 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292947 : y ≠ y ∨ x = (M.op x y) ∨ (τ y) = (τ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq153294 x y
       have i₂ := eq292890
       grind)
    | exact superpose eq292890 eq153294
    | (have j0 := eq153294 x y
       grind)
    | (have r₁ := eq153294 x y
       have r₂ := eq292890
       grind)
    | exact resolve eq153294 eq292890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292890
  have eq292948 : x = (M.op x y) ∨ (τ y) = (τ x) ∨ x = (M.op x x) := by grind
  clear eq292947
  have eq292956 : x = (k x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq292918
       have r₂ := eq13 x y
       grind)
    | (have r₁ := eq292918
       have r₂ := eq13 x x
       grind)
    | exact resolve eq292918 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292918
  have eq294114 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (τ y) = (τ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq292497
       have i₂ := eq292948
       grind)
    | exact superpose eq292948 eq292497
    | exact resolve eq292497 eq292948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292948
  have eq294206 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (τ y) = (τ x) := by grind
  clear eq294114
  have eq294207 : (τ y) = (τ x) ∨ x = (M.op x x) := by grind
  clear eq294206
  have eq294224 : y = (σ (τ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 y
       have i₂ := eq294207
       grind)
    | exact superpose eq294207 eq11
    | exact resolve eq11 eq294207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294207
  have eq294506 : x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq294224
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq294224
    | exact resolve eq294224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294224
  have eq296757 : (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq292609
       have i₂ := eq292956
       grind)
    | exact superpose eq292956 eq292609
    | exact resolve eq292609 eq292956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292609 eq292956
  have eq296761 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq296757
  have eq296817 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq292497
       have i₂ := eq296761
       grind)
    | exact superpose eq296761 eq292497
    | exact resolve eq292497 eq296761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292497 eq296761
  have eq296909 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq296817
  have eq296910 : (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq296909
  have eq296974 : (M.op (σ x) (σ x)) = (σ (k y y)) ∨ (σ x) = (σ (k y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq289 y
       have i₂ := eq296910
       grind)
    | exact superpose eq296910 eq289
    | exact resolve eq289 eq296910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq296910
  have eq297144 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ (k y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq296974
       have i₂ := eq289281
       grind)
    | exact superpose eq289281 eq296974
    | exact resolve eq296974 eq289281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296974
  have eq297145 : x = (M.op x x) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq297144
  have eq297183 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq289358
       have i₂ := eq297145
       grind)
    | exact superpose eq297145 eq289358
    | exact resolve eq289358 eq297145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297417 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq297183
  have eq300152 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq297417
       grind)
    | exact superpose eq297417 eq16
    | exact resolve eq16 eq297417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300157 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq297417
       grind)
    | exact superpose eq297417 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq297417
       grind)
    | exact resolve eq12 eq297417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297417
  have eq300245 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq300157
  have eq300264 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq300245
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq300245
    | exact resolve eq300245 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300245
  have eq300398 : (k x y) = (τ (σ y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq300264
       grind)
    | exact superpose eq300264 eq10
    | exact resolve eq10 eq300264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300264
  have eq300556 : y = (k x y) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq300398
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq300398
    | exact resolve eq300398 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300398
  have eq300616 : y ≠ y ∨ x = (M.op x y) ∨ (τ y) = (τ x) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq153294 x y
       have i₂ := eq300556
       grind)
    | exact superpose eq300556 eq153294
    | (have j0 := eq153294 x y
       grind)
    | (have r₁ := eq153294 x y
       have r₂ := eq300556
       grind)
    | exact resolve eq153294 eq300556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153294 eq300556
  have eq300617 : x = (M.op x y) ∨ (τ y) = (τ x) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq300616
  have eq323545 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y y)) ∨ (τ y) = (τ x) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq300152
       have i₂ := eq300617
       grind)
    | exact superpose eq300617 eq300152
    | exact resolve eq300152 eq300617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300152 eq300617
  have eq323659 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y y)) ∨ (τ y) = (τ x) := by grind
  clear eq323545
  have eq323660 : (τ y) = (τ x) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq323659
  have eq323681 : y = (σ (τ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq11 y
       have i₂ := eq323660
       grind)
    | exact superpose eq323660 eq11
    | exact resolve eq11 eq323660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323660
  have eq323965 : x = y ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq323681
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq323681
    | exact resolve eq323681 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323681
  have eq323966 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq323965
       grind)
    | exact superpose eq323965 eq16
    | exact resolve eq16 eq323965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323965
  have eq324134 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq323966
       have i₂ := eq289281
       grind)
    | exact superpose eq289281 eq323966
    | exact resolve eq323966 eq289281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323966
  have eq324160 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ (k y y)) := by
    first
    | (have i₁ := eq324134
       have i₂ := eq297145
       grind)
    | exact superpose eq297145 eq324134
    | exact resolve eq324134 eq297145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297145 eq324134
  have eq324222 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y y)) := by grind
  clear eq324160
  have eq324223 : (σ x) = (σ (k y y)) := by grind
  clear eq324222
  have eq324622 : (τ (σ x)) = (k y y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq324223
       grind)
    | exact superpose eq324223 eq10
    | exact resolve eq10 eq324223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324223
  have eq324825 : x = (k y y) := by
    first
    | (have i₁ := eq324622
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq324622
    | exact resolve eq324622 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324622
  have eq325582 : x = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq39080 y y
       have i₂ := eq324825
       grind)
    | exact superpose eq324825 eq39080
    | exact resolve eq39080 eq324825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39080 eq324825
  have eq325621 : x = y ∨ x = (M.op y y) := by grind
  clear eq325582
  have eq325740 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq325621
       grind)
    | exact superpose eq325621 eq16
    | exact resolve eq16 eq325621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325621
  have eq325912 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq325740
       have i₂ := eq289281
       grind)
    | exact superpose eq289281 eq325740
    | exact resolve eq325740 eq289281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289281 eq325740
  have eq338309 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ (M.op x x) = (k x x) ∨ (M.op x x) = (k x x) := by
    first
    | (have i₁ := eq325912
       have i₂ := eq191271 x x
       grind)
    | exact superpose eq191271 eq325912
    | (have j1 := eq191271 x x
       grind)
    | exact resolve eq325912 eq191271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191271 eq325912
  have eq338310 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ (M.op x x) = (k x x) := by grind
  clear eq338309
  have eq338311 : x = (M.op y y) ∨ (M.op x x) = (k x x) := by grind
  clear eq338310
  have eq338367 : x = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq338311
       have i₂ := eq259736
       grind)
    | exact superpose eq259736 eq338311
    | exact resolve eq338311 eq259736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259736 eq338311
  have eq338380 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq338367
       have i₂ := eq294506
       grind)
    | exact superpose eq294506 eq338367
    | exact resolve eq338367 eq294506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294506 eq338367
  have eq338669 : x = (M.op x x) := by grind
  clear eq338380
  have eq338722 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq289358
       have i₂ := eq338669
       grind)
    | exact superpose eq338669 eq289358
    | exact resolve eq289358 eq338669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289358
  have eq338984 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq338722
  have eq339480 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq338984
       grind)
    | exact superpose eq338984 eq16
    | exact resolve eq16 eq338984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339486 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq338984
       grind)
    | exact superpose eq338984 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq338984
       grind)
    | exact resolve eq12 eq338984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338984
  have eq339579 : (σ y) = (k (σ x) (σ y)) := by grind
  clear eq339486
  have eq339599 : (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq339579
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq339579
    | exact resolve eq339579 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339579
  have eq339784 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq339599
       grind)
    | exact superpose eq339599 eq10
    | exact resolve eq10 eq339599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339599
  have eq339934 : y = (k x y) := by
    first
    | (have i₁ := eq339784
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq339784
    | exact resolve eq339784 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339784
  have eq340703 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq339934
       have i₂ := eq278 y x
       grind)
    | exact superpose eq278 eq339934
    | (have j1 := eq278 y x
       grind)
    | exact resolve eq339934 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq340744 : x = (M.op x y) ∨ x = (k x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq340703
       have r₂ := eq13 x y
       grind)
    | exact resolve eq340703 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340703
  have eq340748 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq340744
       have i₂ := eq339934
       grind)
    | exact superpose eq339934 eq340744
    | exact resolve eq340744 eq339934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339934 eq340744
  have eq340952 : (σ x) ≠ (σ x) ∨ x = y := by
    first
    | (have i₁ := eq339480
       have i₂ := eq340748
       grind)
    | exact superpose eq340748 eq339480
    | exact resolve eq339480 eq340748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340748
  have eq341055 : x = y := by grind
  clear eq340952
  have eq341266 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq339480
       have i₂ := eq341055
       grind)
    | exact superpose eq341055 eq339480
    | exact resolve eq339480 eq341055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339480 eq341055
  have eq341292 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq341266
       have i₂ := eq338669
       grind)
    | exact superpose eq338669 eq341266
    | exact resolve eq341266 eq338669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338669 eq341266
  have eq341293 : False := by grind
  exact eq341293

/-- `Equation1636`: `x = (x ◇ x) ◇ ((y ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation1636 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1636 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1636.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq60 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq60 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq60 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq200 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq207 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq200 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq200 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq200 X0 X0
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq200 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq200
  have eq550 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq207 (σ X1) (σ X0)
       grind)
    | exact superpose eq207 eq15
    | exact resolve eq15 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X1
       have i₂ := eq207 X1 X0
       grind)
    | exact superpose eq207 eq550
    | exact resolve eq550 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq550
  have eq557 : False := by grind
  exact eq557

/-- `Equation1728`: `x = (y ◇ y) ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyx_pxx_pyx_pxy_Equation1728 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1728 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1728.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
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
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq35
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq102 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq138 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq102 (σ X0) (σ X1)
       grind)
    | exact superpose eq102 eq15
    | (have j1 := eq102 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq102 X0 (τ X1)
       grind)
    | exact superpose eq102 eq18
    | (have j1 := eq102 X0 (τ X1)
       grind)
    | exact resolve eq18 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq102
  have eq147 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq138
    | (have j0 := eq138 X0 X1
       grind)
    | exact resolve eq138 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq138
  have eq1103 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq143 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq143
    | exact resolve eq143 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq1141 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1103 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1103
    | (have j0 := eq1103 X0 X1
       grind)
    | exact resolve eq1103 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq2281 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq147 x y
       grind)
    | exact superpose eq147 eq16
    | (have j1 := eq147 x y
       grind)
    | exact resolve eq16 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2336 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq2382 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2281
       have i₂ := eq1141 y x
       grind)
    | exact superpose eq1141 eq2281
    | (have j1 := eq1141 y x
       grind)
    | (have r₁ := eq2281
       have r₂ := eq1141 y x
       grind)
    | exact resolve eq2281 eq1141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281
  have eq2383 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2382
  have eq2386 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2383
       grind)
    | exact superpose eq2383 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2383
       grind)
    | exact resolve eq12 eq2383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2383
  have eq2395 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2386
  have eq2451 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2336 x y
       have i₂ := eq2395
       grind)
    | exact superpose eq2395 eq2336
    | (have j0 := eq2336 x y
       grind)
    | exact resolve eq2336 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336 eq2395
  have eq2462 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2451
  have eq2463 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2462
  have eq2505 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2463
       grind)
    | exact superpose eq2463 eq16
    | exact resolve eq16 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2506 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq78 x (σ y)
       have i₂ := eq2463
       grind)
    | exact superpose eq2463 eq78
    | (have j0 := eq78 x (σ y)
       grind)
    | (have r₁ := eq78 x (σ y)
       have r₂ := eq2463
       grind)
    | exact resolve eq78 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq2463
  have eq2521 : (k (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq2506
  have eq2528 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2521
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2521
    | exact resolve eq2521 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2521
  have eq2568 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1141 y x
       have i₂ := eq2528
       grind)
    | exact superpose eq2528 eq1141
    | (have j0 := eq1141 y x
       grind)
    | exact resolve eq1141 eq2528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141 eq2528
  have eq2618 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2568
       have r₂ := eq2505
       grind)
    | exact resolve eq2568 eq2505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568
  have eq2835 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2505
       have i₂ := eq2618
       grind)
    | exact superpose eq2618 eq2505
    | exact resolve eq2505 eq2618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505 eq2618
  have eq2848 : False := by grind
  exact eq2848
