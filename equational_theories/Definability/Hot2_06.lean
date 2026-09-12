import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_y_pxy_y_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
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
  have eq76 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq107 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq84
    | (have j0 := eq84 (σ X0) (σ X1)
       grind)
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq126 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq123
    | exact resolve eq123 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq127 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126
    | exact resolve eq126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq194 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq84
    | (have j0 := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq84 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq194
    | exact resolve eq194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq198 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq195
       have r₂ := eq27
       grind)
    | exact resolve eq195 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq200 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq198
    | exact resolve eq198 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq200 eq27
    | exact resolve eq27 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq200 eq77
    | (have r₁ := eq77
       have r₂ := eq200
       grind)
    | exact resolve eq77 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq200
  have eq514 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq513
  have eq517 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq514 eq127
    | exact resolve eq127 eq514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq521 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq517
  have eq526 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq521
       have r₂ := eq202
       grind)
    | exact resolve eq521 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq521
  have eq531 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq526 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq537 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq84 (σ x) (σ y)
       grind)
    | (have r₁ := eq531
       have r₂ := eq84 (σ x) (σ y)
       grind)
    | exact resolve eq531 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq541 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq537
    | exact resolve eq537 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq541 eq127
    | exact resolve eq127 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq541
  have eq629 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq626
  have eq633 : y = (M.op x y) := by
    first
    | (have r₁ := eq629
       have r₂ := eq27
       grind)
    | exact resolve eq629 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq635 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq633 eq20
    | exact resolve eq20 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : y ≠ y ∨ y = (M.op y x) ∨ y = (k x y) := by
    first
    | exact superpose eq633 eq76
    | (have r₁ := eq76
       have r₂ := eq633
       grind)
    | exact resolve eq76 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq643 : y = (k x y) ∨ y = (M.op y x) := by grind
  clear eq638
  have eq649 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq635
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq635
    | exact resolve eq635 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq683 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq107
    | (have j0 := eq107 X0 (M.op x y)
       grind)
    | exact resolve eq107 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq107
  have eq693 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq633 eq683
    | (have j0 := eq683 X0
       grind)
    | exact resolve eq683 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq717 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq649 eq26
    | exact resolve eq26 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq904 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq643
       grind)
    | exact superpose eq643 eq44
    | exact resolve eq44 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq911 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq649 eq904
    | exact resolve eq904 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904
  have eq913 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq911
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq911
    | exact resolve eq911 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq914 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq649 eq913
    | exact resolve eq913 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq970 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq914 eq84
    | (have j0 := eq84 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq84 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq971 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq970
  have eq973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq717 eq971
    | exact resolve eq971 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq976 : y = (M.op y x) := by
    first
    | (have r₁ := eq973
       have r₂ := eq27
       grind)
    | exact resolve eq973 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq982 : y ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq976
       grind)
    | exact superpose eq976 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq994 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq84 x y
       grind)
    | (have r₁ := eq982
       have r₂ := eq84 x y
       grind)
    | exact resolve eq982 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq982
  have eq1002 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq994
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq994
    | exact resolve eq994 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq994
  have eq1006 : y = (k x y) := by
    first
    | exact superpose eq633 eq1002
    | exact resolve eq1002 eq633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633 eq1002
  have eq1024 : (σ (k x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq693 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq693
    | (have j0 := eq693 x
       grind)
    | exact resolve eq693 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq693
  have eq1042 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq717 eq1024
    | exact resolve eq1024 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1057 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1042
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq1042
    | exact resolve eq1042 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1066 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq649 eq1057
    | exact resolve eq1057 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq1071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq717 eq1066
    | exact resolve eq1066 eq717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq1066
  have eq1074 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq1071
       have r₂ := eq27
       grind)
    | exact resolve eq1071 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1094 : (σ y) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1006
       grind)
    | exact superpose eq1006 eq44
    | exact resolve eq44 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1006
  have eq1101 : (σ y) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq649 eq1094
    | exact resolve eq1094 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094
  have eq1103 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1074 eq1101
    | exact resolve eq1101 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq1101
  have eq1104 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1103
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1103
    | exact resolve eq1103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1103
  have eq1105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq649 eq1104
    | exact resolve eq1104 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq1104
  have eq1106 : False := by grind
  exact eq1106

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_x_pxx_x_pyx_Equation4521 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq33 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq28 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28
    | (have j0 := eq28 x
       grind)
    | exact resolve eq28 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
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
  have eq55 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 x X0 X1 y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 X1 X2 x
       have i₂ := eq9 X0 X3 X4 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (M.op (M.op x y) y) = (M.op x (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq55
    | (have j0 := eq55 (σ x) (σ y)
       grind)
    | exact resolve eq55 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op x (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq84 eq55
    | exact resolve eq55 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq109 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op X2 X3)) = (M.op (M.op (σ x) (M.op X0 X1)) (σ y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (M.op x (M.op (σ x) (σ y))) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq93 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | (have j0 := eq93 x y
       grind)
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq127 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq112 eq84
    | exact resolve eq84 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq112
  have eq134 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X2 X3) (M.op X2 X3)) ∨ (M.op (M.op X2 X3) (M.op X2 X3)) = (k (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X2 X3) X0
       have i₂ := eq9 X0 X2 X3 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X2 X3) X0
       grind)
    | (have r₁ := eq12 (M.op X1 X2) (M.op (M.op X1 X2) (M.op X1 X2))
       have r₂ := eq9 (M.op X1 X2) X1 X2 (M.op X1 X2)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq59 eq12
    | (have j0 := eq12 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq138 (σ X0)
       grind)
    | exact superpose eq138 eq15
    | exact resolve eq15 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq156 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq155 X0
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq155
    | exact resolve eq155 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq223 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq228 : ∀ X0 X1 : G, (σ (k (k X0 (τ X1)) x)) = (k (k (σ X0) X1) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq30
    | exact resolve eq30 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq265 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq156 X0
       grind)
    | exact superpose eq156 eq10
    | exact resolve eq10 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (σ (k (M.op X0 X0) x)) = (k (M.op (σ X0) (σ X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq30 (M.op X0 X0)
       have i₂ := eq156 X0
       grind)
    | exact superpose eq156 eq30
    | exact resolve eq30 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq276 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq223 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq223
    | exact resolve eq223 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq308 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq265 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq265
    | exact resolve eq265 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq482 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X1 X2 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 X0 X1 X2 x y
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq26 eq58
    | (have j0 := eq58 X0 X1 X2 (σ x) (σ y)
       grind)
    | exact resolve eq58 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq546 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X3
    first
    | (have i₁ := eq9 X0 x x X3
       have i₂ := eq486 X0 x x
       grind)
    | (have i₁ := eq9 X0 (σ x) (σ y) X3
       have i₂ := eq486 X0 x x
       grind)
    | exact superpose eq486 eq9
    | (have j0 := eq9 X0 (σ x) (σ y) X3
       grind)
    | exact resolve eq9 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X2 X3) (M.op (σ x) (σ y))) ∨ (M.op (M.op X2 X3) (M.op X2 X3)) = (k (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq134 X0 X1 X2 X3
       have i₂ := eq486 (M.op X2 X3) X2 X3
       grind)
    | (have i₁ := eq134 X0 X1 (σ x) (σ y)
       have i₂ := eq486 (M.op (σ x) (σ y)) X1 X2
       grind)
    | exact superpose eq486 eq134
    | (have j0 := eq134 X0 X1 X2 X3
       grind)
    | (have r₁ := eq134 X1 (M.op (σ x) (σ y)) X1 (M.op (σ x) (σ y))
       have r₂ := eq486 (M.op X1 (M.op (σ x) (σ y))) X1 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq134 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq572 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq59 x x
       have i₂ := eq486 sF2 x x
       grind)
    | (have i₁ := eq59 (σ x) (σ y)
       have i₂ := eq486 sF2 x x
       grind)
    | exact superpose eq486 eq59
    | (have j0 := eq59 (σ x) (σ y)
       grind)
    | exact resolve eq59 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq573 : ∀ X2 X3 : G, (M.op (M.op (σ x) (σ y)) (M.op X2 X3)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    intro X2 X3
    first
    | (have i₁ := eq109 x X2 X2 X3
       have i₂ := eq486 sF2 x X2
       grind)
    | (have i₁ := eq109 (σ x) (σ y) X2 X3
       have i₂ := eq486 sF2 x X2
       grind)
    | exact superpose eq486 eq109
    | (have j0 := eq109 (σ x) (σ y) X2 X3
       grind)
    | exact resolve eq109 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq574 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq137 x x
       have i₂ := eq486 sF2 x x
       grind)
    | (have i₁ := eq137 (σ x) (σ y)
       have i₂ := eq486 sF2 x x
       grind)
    | exact superpose eq486 eq137
    | (have j0 := eq137 (σ x) (σ y)
       grind)
    | exact resolve eq137 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq580 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq482 X0 x x
       have i₂ := eq486 X0 x x
       grind)
    | (have i₁ := eq482 X0 (σ x) (σ y)
       have i₂ := eq486 X0 x x
       grind)
    | exact superpose eq486 eq482
    | (have j0 := eq482 X0 (σ x) (σ y)
       have j1 := eq486 X0 x y
       grind)
    | exact resolve eq482 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq621 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | (have i₁ := eq573 x x
       have i₂ := eq486 sF4 x x
       grind)
    | (have i₁ := eq573 (σ x) (σ y)
       have i₂ := eq486 sF4 x x
       grind)
    | exact superpose eq486 eq573
    | (have j0 := eq573 (σ x) (σ y)
       grind)
    | exact resolve eq573 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq633 : ∀ X0 X1 X2 X3 : G, (k (M.op X2 X3) X0) = (M.op (M.op X2 X3) (M.op (σ x) (σ y))) ∨ (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X2 X3) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq561 X0 X1 X2 X3
       have i₂ := eq486 (M.op X2 X3) X2 X3
       grind)
    | (have i₁ := eq561 X0 X1 (σ x) (σ y)
       have i₂ := eq486 (M.op (σ x) (σ y)) X1 X2
       grind)
    | exact superpose eq486 eq561
    | (have j0 := eq561 X0 X1 X2 X3
       grind)
    | (have r₁ := eq561 X0 (M.op X1 X2) X0 (M.op X1 X2)
       have r₂ := eq486 (M.op X0 (M.op X1 X2)) X1 X2
       grind)
    | (have r₁ := eq561 X0 (M.op (σ x) (σ y)) X0 (M.op (σ x) (σ y))
       have r₂ := eq486 (M.op X0 (M.op (σ x) (σ y))) (σ x) (σ y)
       grind)
    | exact resolve eq561 eq486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486 eq561
  have eq653 : ∀ X0 X3 : G, (M.op (M.op X0 X3) X3) = (M.op X0 (M.op x y)) := by
    intro X0 X3
    first
    | exact superpose eq580 eq546
    | exact resolve eq546 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq660 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq580 eq572
    | exact resolve eq572 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq661 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (M.op x y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq580 eq574
    | exact resolve eq574 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq703 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op x y)) (σ y)) := by
    first
    | exact superpose eq580 eq621
    | exact resolve eq621 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq714 : ∀ X0 X1 X2 X3 : G, (k (M.op X2 X3) X0) = (M.op (M.op X2 X3) (M.op x y)) ∨ (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X2 X3) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq580 eq633
    | (have j0 := eq633 X0 X1 X2 X3
       grind)
    | (have r₁ := eq633 X0 (M.op x y) X0 (M.op x y)
       have r₂ := eq580 (M.op X0 (M.op x y))
       grind)
    | exact resolve eq633 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq739 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (M.op x y)) (σ y)) := by
    first
    | exact superpose eq580 eq703
    | exact resolve eq703 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq747 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X2 X3) (M.op x y)) ∨ (k (M.op X2 X3) X0) = (M.op (M.op X2 X3) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq580 eq714
    | (have j0 := eq714 X0 X1 X2 X3
       grind)
    | (have r₁ := eq714 X0 (M.op x y) X0 (M.op x y)
       have r₂ := eq580 (M.op X0 (M.op x y))
       grind)
    | exact resolve eq714 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714
  have eq769 : ∀ X0 X2 X3 : G, (M.op X0 (M.op x y)) ≠ (M.op (M.op X2 X3) (M.op x y)) ∨ (k (M.op X2 X3) X0) = (M.op (M.op X2 X3) (M.op x y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq747 X0 x X2 X3
       have i₂ := eq653 X0 x
       grind)
    | exact superpose eq653 eq747
    | (have j0 := eq747 X0 x X2 X3
       grind)
    | (have r₁ := eq747 (M.op X2 X3) X3 X2 X3
       have r₂ := eq653 (M.op X2 X3) X3
       grind)
    | (have r₁ := eq747 X0 (M.op x y) (M.op X0 (M.op x y)) (M.op x y)
       have r₂ := eq653 (M.op X0 (M.op x y)) (M.op x y)
       grind)
    | exact resolve eq747 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq812 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq62
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq62
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq812
    | exact resolve eq812 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq818 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq816
    | exact resolve eq816 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq820 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq818
    | exact resolve eq818 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq1966 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op X1 (M.op x y)) ∨ (M.op X0 (M.op x y)) = (k (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq769 X0 X0 sF0
       have i₂ := eq653 X0 sF0
       grind)
    | exact superpose eq653 eq769
    | (have r₁ := eq769 (M.op (M.op x x) (M.op x y)) x x
       have r₂ := eq653 (M.op x x) (M.op x y)
       grind)
    | (have r₁ := eq769 X0 X0 (M.op x y)
       have r₂ := eq653 X0 (M.op x y)
       grind)
    | exact resolve eq769 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq2156 : (σ (k (M.op (M.op x y) (M.op x y)) x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq20 eq270
    | (have j0 := eq270 (M.op x y)
       grind)
    | exact resolve eq270 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq820
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq820
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq820 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2976
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2976
    | exact resolve eq2976 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq3005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq3002
    | exact resolve eq3002 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002
  have eq3006 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq3005
       have r₂ := eq27
       grind)
    | exact resolve eq3005 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3005
  have eq3007 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3006
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3006
    | exact resolve eq3006 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3006
  have eq3008 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3007
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3007
    | exact resolve eq3007 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3007
  have eq3019 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq3008 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3008
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3008
       grind)
    | exact resolve eq12 eq3008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3008
  have eq3677 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq3019
    | (have j0 := eq3019 (σ x)
       grind)
    | (have r₁ := eq3019 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq3019 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3019
  have eq3682 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq3677
  have eq3685 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq62 eq3682
    | exact resolve eq3682 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3682
  have eq3687 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3685
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq3685
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq3685 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685
  have eq3716 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3687
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3687
    | exact resolve eq3687 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3687
  have eq3719 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq3716
    | exact resolve eq3716 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716
  have eq3720 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq3719
       have r₂ := eq27
       grind)
    | exact resolve eq3719 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3719
  have eq3721 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3720
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3720
    | exact resolve eq3720 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3720
  have eq3722 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq3721
  have eq3723 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3722
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3722
    | exact resolve eq3722 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3722
  have eq3724 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3723
  have eq3728 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq156 y
       have i₂ := eq3724
       grind)
    | exact superpose eq3724 eq156
    | exact resolve eq156 eq3724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq3729 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq3724
       grind)
    | exact superpose eq3724 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq3724
       grind)
    | exact resolve eq12 eq3724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq3738 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3728
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3728
    | exact resolve eq3728 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3728
  have eq3740 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3738
    | exact resolve eq3738 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3738
  have eq4709 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op X0 (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq1966 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966
  have eq4738 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3729 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3729
    | (have j0 := eq3729 x
       grind)
    | (have r₁ := eq3729 x
       have r₂ := eq18
       grind)
    | exact resolve eq3729 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3729
  have eq4743 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4738
  have eq4747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq820
       have i₂ := eq4743
       grind)
    | exact superpose eq4743 eq820
    | exact resolve eq820 eq4743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4743
  have eq4751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4747
  have eq4754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq4751
    | exact resolve eq4751 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4751
  have eq4756 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4754
       have r₂ := eq27
       grind)
    | exact resolve eq4754 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4754
  have eq4775 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4756 eq3740
    | exact resolve eq3740 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3740 eq4756
  have eq4791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4775
  have eq4797 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4791
       have r₂ := eq27
       grind)
    | exact resolve eq4791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4791
  have eq4801 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4797 eq580
    | exact resolve eq580 eq4797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq4802 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4797 eq660
    | exact resolve eq660 eq4797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq4848 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4801 eq26
    | (have j1 := eq4801 (σ x)
       grind)
    | exact resolve eq26 eq4801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4909 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4848 eq653
    | exact resolve eq653 eq4848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq4918 : (σ y) = (M.op (σ y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4797 eq4909
    | exact resolve eq4909 eq4797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4938 : (σ y) = (M.op (σ y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq4918
  have eq4973 : (M.op (σ x) (M.op x y)) ≠ (M.op (σ x) (M.op x y)) ∨ (k (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4802 eq661
    | (have r₁ := eq661
       have r₂ := eq4802
       grind)
    | exact resolve eq661 eq4802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4983 : (M.op (σ x) (M.op x y)) = (M.op (σ y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4802 eq4801
    | exact resolve eq4801 eq4802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4801 eq4802
  have eq4998 : (M.op (σ x) (M.op x y)) = (M.op (σ y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq4983
  have eq5002 : (k (σ y) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq4973
  have eq5043 : (σ y) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4998 eq4938
    | exact resolve eq4938 eq4998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4938 eq4998
  have eq5066 : (σ y) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq5043
  have eq5073 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5066 eq739
    | exact resolve eq739 eq5066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq5231 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5073 eq4909
    | exact resolve eq4909 eq5073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4909 eq5073
  have eq5251 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5231
  have eq5265 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5251 eq661
    | exact resolve eq661 eq5251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq5251
  have eq5300 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5265
       have r₂ := eq4848
       grind)
    | exact resolve eq5265 eq4848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4848 eq5265
  have eq5301 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4797 eq5300
    | exact resolve eq5300 eq4797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5309 : (τ (M.op (σ x) (σ y))) = (k (τ (σ y)) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5300 eq276
    | exact resolve eq276 eq5300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276 eq5300
  have eq5314 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5301
  have eq5315 : (τ (M.op (σ x) (σ y))) = (k y (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39 eq5309
    | exact resolve eq5309 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309
  have eq5318 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5314
       have i₂ := eq138 sF3
       grind)
    | exact superpose eq138 eq5314
    | exact resolve eq5314 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq5314
  have eq5340 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5318 eq308
    | exact resolve eq308 eq5318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq5318
  have eq5365 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39 eq5340
    | exact resolve eq5340 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5340
  have eq5511 : (k (k (σ y) (M.op (σ x) (σ y))) (σ x)) = (σ (k (τ (M.op (σ x) (σ y))) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5315 eq228
    | exact resolve eq228 eq5315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq5315
  have eq5529 : (k (k (σ y) (M.op (σ x) (σ y))) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5511
       have i₂ := eq49 sF4 x
       grind)
    | exact superpose eq49 eq5511
    | exact resolve eq5511 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq5511
  have eq5542 : (k (M.op (σ x) (σ y)) (σ x)) = (k (k (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5529
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5529
    | exact resolve eq5529 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5529
  have eq5552 : (k (M.op (σ x) (σ y)) (σ x)) = (k (k (σ y) (M.op (σ x) (σ y))) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5542
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5542
    | exact resolve eq5542 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5542
  have eq23031 : (k (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5002 eq5552
    | exact resolve eq5552 eq5002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5002 eq5552
  have eq23057 : (k (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (M.op x y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq23031
  have eq23064 : (M.op (σ x) (M.op x y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4709 eq23057
    | exact resolve eq23057 eq4709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23057
  have eq23072 : (k (σ y) (σ x)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4797 eq23064
    | exact resolve eq23064 eq4797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4797 eq23064
  have eq23084 : (k (σ y) (σ x)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq23072
  have eq23086 : (σ (k y x)) = (M.op (σ x) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq62 eq23084
    | exact resolve eq23084 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq23084
  have eq23121 : (k y x) = (τ (M.op (σ x) (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq23086
       grind)
    | exact superpose eq23086 eq10
    | exact resolve eq10 eq23086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23086
  have eq24494 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5066 eq23121
    | exact resolve eq23121 eq5066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5066 eq23121
  have eq24534 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq24494
  have eq24536 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq39 eq24534
    | exact resolve eq24534 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq24534
  have eq24546 : y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq24536
       grind)
    | exact superpose eq24536 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq24536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24536
  have eq24555 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq24546
  have eq24568 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24555
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24555
    | exact resolve eq24555 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24555
  have eq24569 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq24568
  have eq24582 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq24569
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq24569
    | exact resolve eq24569 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24569
  have eq24610 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5365
       have i₂ := eq24582
       grind)
    | exact superpose eq24582 eq5365
    | exact resolve eq5365 eq24582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5365 eq24582
  have eq24640 : y = (M.op x y) := by grind
  clear eq24610
  have eq24649 : y = (M.op x y) := by
    first
    | exact superpose eq24640 eq18
    | exact resolve eq18 eq24640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24650 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq24640 eq20
    | exact resolve eq20 eq24640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq24653 : (k (σ (M.op x y)) (σ x)) = (σ (k y x)) := by
    first
    | exact superpose eq24640 eq33
    | exact resolve eq33 eq24640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq24658 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq24640 eq127
    | exact resolve eq127 eq24640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq24940 : (σ (k (M.op y y) x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq24640 eq2156
    | exact resolve eq2156 eq24640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156
  have eq25266 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) X0) := by
    intro X0
    first
    | exact superpose eq24640 eq4709
    | exact resolve eq4709 eq24640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4709 eq24640
  have eq26449 : (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) = (σ (k (M.op x y) x)) := by
    first
    | (have i₁ := eq24940
       have i₂ := eq24658
       grind)
    | exact superpose eq24658 eq24940
    | exact resolve eq24940 eq24658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24940
  have eq26463 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24650
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24650
    | exact resolve eq24650 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24650
  have eq26464 : y = (M.op y y) := by
    first
    | (have i₁ := eq24658
       have i₂ := eq24649
       grind)
    | exact superpose eq24649 eq24658
    | exact resolve eq24658 eq24649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24658
  have eq26782 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq26449
       have i₂ := eq25266 x
       grind)
    | exact superpose eq25266 eq26449
    | exact resolve eq26449 eq25266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25266 eq26449
  have eq26802 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq26463 eq24
    | exact resolve eq24 eq26463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq26803 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq26463 eq26
    | exact resolve eq26 eq26463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq26817 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26463 eq820
    | exact resolve eq820 eq26463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq27680 : (σ y) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq26782
       have i₂ := eq24649
       grind)
    | exact superpose eq24649 eq26782
    | exact resolve eq26782 eq24649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24649 eq26782
  have eq27964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | exact superpose eq26463 eq26817
    | exact resolve eq26817 eq26463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26463 eq26817
  have eq28102 : (σ (M.op x y)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq27680
       have i₂ := eq26802
       grind)
    | exact superpose eq26802 eq27680
    | exact resolve eq27680 eq26802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27680
  have eq28377 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq27964
       have r₂ := eq27
       grind)
    | exact resolve eq27964 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27964
  have eq28722 : (σ (k (M.op y y) x)) = (k (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq270 y
       have i₂ := eq26802
       grind)
    | exact superpose eq26802 eq270
    | exact resolve eq270 eq26802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq26802
  have eq28732 : (σ (M.op x y)) = (σ (k (M.op y y) x)) := by
    first
    | exact superpose eq28102 eq28722
    | exact resolve eq28722 eq28102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28102 eq28722
  have eq28733 : (σ (M.op x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq28732
       have i₂ := eq26464
       grind)
    | exact superpose eq26464 eq28732
    | exact resolve eq28732 eq26464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26464 eq28732
  have eq28734 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq24653
       have i₂ := eq28733
       grind)
    | exact superpose eq28733 eq24653
    | exact resolve eq24653 eq28733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24653
  have eq28751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq28377
       have i₂ := eq28733
       grind)
    | exact superpose eq28733 eq28377
    | exact resolve eq28377 eq28733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28377 eq28733
  have eq28753 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq28751
       have r₂ := eq27
       grind)
    | exact resolve eq28751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28751
  have eq28851 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26803 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq12 eq26803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26803
  have eq28853 : (k (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq28851
       have r₂ := eq28753
       grind)
    | exact resolve eq28851 eq28753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28851
  have eq28854 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq28753 eq28853
    | exact resolve eq28853 eq28753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28753 eq28853
  have eq28855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28734 eq28854
    | exact resolve eq28854 eq28734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28734 eq28854
  have eq28856 : False := by grind
  exact eq28856

/-- `Equation4523`: `x ◇ (y ◇ z) = (y ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_pyy_pxy_Equation4523 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4523 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4523.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 x)
       have i₂ := eq9 X1 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X3) X3) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X0) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X2) X1 X3
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X0) X3)) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op X1 X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 X1 X2 : G, (k (M.op X0 X2) X1) = (M.op (M.op X0 X2) X1) ∨ (M.op (M.op X0 X1) X1) ≠ (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X2) X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X0 X2) X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq60
    | (have j0 := eq60 (σ X0) (σ X1)
       grind)
    | exact resolve eq60 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq60 (τ X0) X1
       grind)
    | exact superpose eq60 eq17
    | (have j1 := eq60 (τ X0) X1
       grind)
    | exact resolve eq17 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq77 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq60 X0 (τ X1)
       grind)
    | exact superpose eq60 eq18
    | (have j1 := eq60 X0 (τ X1)
       grind)
    | exact resolve eq18 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X0) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X1 X2 X0
       have i₂ := eq27 X0 (M.op X1 X2) X2 X3
       grind)
    | (have i₁ := eq23 X1 X2 X0
       have i₂ := eq27 X0 (M.op X1 X2) X3 X2
       grind)
    | exact superpose eq27 eq23
    | exact resolve eq23 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1 X2
       have i₂ := eq9 X2 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 X2) (M.op X1 X4))) = (M.op (M.op (M.op (M.op X0 X1) X1) X3) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X0 X2) X1 X4 X3
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op X3 X1) X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X1 X3 x X0
       have i₂ := eq27 X0 X1 (M.op X3 x) X2
       grind)
    | (have i₁ := eq24 X1 X3 x X0
       have i₂ := eq27 X0 X1 X2 (M.op X3 x)
       grind)
    | exact superpose eq27 eq24
    | exact resolve eq24 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X3))) ≠ X0 ∨ (k X0 (M.op (M.op X2 X1) X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 (M.op (M.op X2 X1) X0)
       have i₂ := eq24 X1 X2 X3 X0
       grind)
    | exact superpose eq24 eq12
    | (have j0 := eq12 X0 (M.op (M.op X2 X1) X0)
       grind)
    | exact resolve eq12 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 X1 (M.op X0 X2) X3
       have i₂ := eq24 (M.op X1 (M.op X0 X2)) X0 X2 X3
       grind)
    | exact superpose eq24 eq23
    | exact resolve eq23 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq245 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X2) X3) X3) = (M.op (M.op (M.op (M.op X1 X0) X0) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq236 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 (M.op X0 X2)
       grind)
    | exact superpose eq9 eq236
    | exact resolve eq236 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq293 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26 X0 X1 X2 X0
       have i₂ := eq23 X1 X0 X0
       grind)
    | exact superpose eq23 eq26
    | exact resolve eq26 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X1 X0) X3) X0) = (M.op (M.op (M.op X1 X0) X3) X0) ∨ (M.op (M.op X1 X0) X3) ≠ (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op (M.op X1 X0) X3) X0
       have i₂ := eq26 X0 X1 X2 X3
       grind)
    | exact superpose eq26 eq12
    | (have j0 := eq12 (M.op (M.op X1 X0) X3) X0
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq343 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X3) (M.op X0 X4))) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 (M.op X1 X3) X0 X4 X0
       have i₂ := eq26 X0 X1 X3 X2
       grind)
    | exact superpose eq26 eq24
    | exact resolve eq24 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq357 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X0) = (M.op (M.op (M.op X1 X3) X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq343 X0 X1 X2 X3 x
       have i₂ := eq9 X0 (M.op X1 X3) (M.op X0 x)
       grind)
    | exact superpose eq9 eq343
    | exact resolve eq343 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq453 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 (M.op X0 X4)) X2) = (M.op X2 (M.op (M.op (M.op X0 X1) X1) (M.op X0 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq26 X2 X0 X4 (M.op X1 x)
       have i₂ := eq25 X0 X1 X2 x
       grind)
    | exact superpose eq25 eq26
    | exact resolve eq26 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq506 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 (M.op X0 X4)) X2) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq453 X0 X1 X2 X4
       have i₂ := eq9 X2 (M.op (M.op X0 X1) X1) (M.op X0 X2)
       grind)
    | exact superpose eq9 eq453
    | exact resolve eq453 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq576 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq617 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 (τ X2)) (τ X2)) ∨ (k (σ (M.op X0 X1)) X2) = (σ (M.op (M.op X0 X1) (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (M.op X0 X1)
       have i₂ := eq36 X0 (τ X2) X1
       grind)
    | exact superpose eq36 eq18
    | (have j1 := eq36 X0 (τ X2) X1
       grind)
    | exact resolve eq18 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq36
  have eq716 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq77
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 (τ X0))) X0) = (σ (M.op (τ X0) (M.op X1 X2))) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq77 (M.op X1 (τ X1)) X1
       have i₂ := eq9 (τ X1) X1 X2
       grind)
    | exact superpose eq9 eq77
    | exact resolve eq77 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq743 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq716 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq716
    | (have j0 := eq716 X0 X1
       grind)
    | exact resolve eq716 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq795 : ∀ X0 X1 X2 X3 : G, (σ (M.op (τ X0) (M.op X1 X2))) = (k X0 (σ (M.op X1 X3))) ∨ (τ X0) = (M.op (τ X0) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75 X0 (M.op X1 X2)
       have i₂ := eq27 (τ X0) X1 X2 X3
       grind)
    | (have i₁ := eq75 X0 (M.op X1 X3)
       have i₂ := eq27 (τ X0) X1 X2 X3
       grind)
    | exact superpose eq27 eq75
    | (have j0 := eq75 X0 (M.op X1 X2)
       grind)
    | exact resolve eq75 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq75
  have eq828 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq576
       have i₂ := eq60 x y
       grind)
    | exact superpose eq60 eq576
    | (have j1 := eq60 (σ x) (σ y)
       grind)
    | exact resolve eq576 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq831 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq828
  have eq1490 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq142 (M.op X2 X0) X0 X3
       have i₂ := eq23 X1 X2 X0
       grind)
    | exact superpose eq23 eq142
    | exact resolve eq142 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1600 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1490 X0 X1 X2 X3
       have i₂ := eq142 X0 (M.op (M.op X1 X2) X2) X3
       grind)
    | exact superpose eq142 eq1490
    | exact resolve eq1490 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq1615 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op X2 X3) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1600 X0 x X2 X3
       have i₂ := eq142 (M.op x X2) X2 X3
       grind)
    | exact superpose eq142 eq1600
    | exact resolve eq1600 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1761 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 X4)) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X3) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq217 X3 X0 X4 (M.op X2 X0)
       have i₂ := eq23 X1 X2 X0
       grind)
    | exact superpose eq23 eq217
    | exact resolve eq217 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq217
  have eq1958 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 X4)) = (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1761 X0 X1 X2 X3 X4
       have i₂ := eq142 X0 (M.op (M.op X1 X2) X2) X3
       grind)
    | exact superpose eq142 eq1761
    | exact resolve eq1761 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1761
  have eq2001 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 X4)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq1958 X0 x X2 X3 X4
       have i₂ := eq142 (M.op x X2) X2 X3
       grind)
    | exact superpose eq142 eq1958
    | exact resolve eq1958 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1958
  have eq9156 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op (M.op X0 X2) X3) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq245 X0 x X2 X3
       have i₂ := eq142 (M.op x X0) X0 X3
       grind)
    | exact superpose eq142 eq245
    | exact resolve eq245 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq10168 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq357 X0 X1 X2 x
       have i₂ := eq9156 X1 x X0
       grind)
    | exact superpose eq9156 eq357
    | exact resolve eq357 eq9156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq10169 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10168 X0 X1 x
       have i₂ := eq293 X0 (M.op X1 X0) x
       grind)
    | exact superpose eq293 eq10168
    | exact resolve eq10168 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq10168
  have eq11709 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 X2) X2) = (M.op (M.op X2 (M.op X0 X4)) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq506 X0 X1 X2 X4
       have i₂ := eq142 (M.op X0 X1) X1 X2
       grind)
    | exact superpose eq142 eq506
    | exact resolve eq506 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq18696 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 X2) (M.op X1 X4))) = (M.op (M.op X1 X3) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq182 X0 X1 X2 X3 X4
       have i₂ := eq142 (M.op X0 X1) X1 X3
       grind)
    | exact superpose eq142 eq182
    | exact resolve eq182 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq133907 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X0) = (k X0 (M.op (M.op X2 X1) X0)) ∨ (M.op X0 (M.op X1 (M.op X2 X3))) ≠ X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq226 X0 X1 X2 X3
       have i₂ := eq140 X0 X2 X1 X0
       grind)
    | exact superpose eq140 eq226
    | (have j0 := eq226 X0 X1 X2 X3
       grind)
    | exact resolve eq226 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq226
  have eq432477 : ∀ X0 X1 X2 X3 : G, (k X0 (τ (σ (M.op X1 X3)))) = (τ (σ (M.op (τ (σ X0)) (M.op X1 X2)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33 X0 (σ (M.op X1 X3))
       have i₂ := eq795 (σ X0) X1 X2 X3
       grind)
    | exact superpose eq795 eq33
    | (have j1 := eq795 (σ X0) X1 X2 X3
       grind)
    | exact resolve eq33 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq795
  have eq432509 : ∀ X0 X1 X2 X3 : G, (M.op (τ (σ X0)) (M.op X1 X2)) = (k X0 (τ (σ (M.op X1 X3)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq432477 X0 X1 X2 X3
       have i₂ := eq10 (M.op (τ (σ X0)) (M.op X1 X2))
       grind)
    | exact superpose eq10 eq432477
    | (have j0 := eq432477 X0 X1 X2 X3
       grind)
    | exact resolve eq432477 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432477
  have eq432575 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op X1 X3)) = (M.op (τ (σ X0)) (M.op X1 X2)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq432509 X0 X1 X2 X3
       have i₂ := eq10 (M.op X1 X3)
       grind)
    | exact superpose eq10 eq432509
    | (have j0 := eq432509 X0 X1 X2 X3
       grind)
    | exact resolve eq432509 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432509
  have eq432608 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X3)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq432575 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq432575
    | (have j0 := eq432575 X0 X1 X2 X3
       grind)
    | exact resolve eq432575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432575
  have eq432614 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq432608 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq432608
    | (have j0 := eq432608 X0 X1 X2 X3
       grind)
    | exact resolve eq432608 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432608
  have eq432954 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X1) = X1 ∨ (M.op (M.op X0 X1) X1) = (k X1 (M.op X2 X4)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq432614 x X0 X4 x
       have i₂ := eq2001 X0 X2 x X4
       grind)
    | exact superpose eq2001 eq432614
    | exact resolve eq432614 eq2001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433204 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X0) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq432614 X0 X1 X2 X3
       grind)
    | exact superpose eq432614 eq9
    | (have j1 := eq432614 X0 X1 X2 X3
       grind)
    | exact resolve eq9 eq432614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443323 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9156 X1 X0 X0
       have i₂ := eq433204 X0 X1 X2 X3
       grind)
    | exact superpose eq433204 eq9156
    | (have j1 := eq433204 X0 X1 X2 X3
       grind)
    | exact resolve eq9156 eq433204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9156 eq433204
  have eq444946 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq443323 X0 X1 X2 X3
       grind)
    | exact superpose eq443323 eq12
    | (have j1 := eq443323 X0 X1 X2 X3
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq443323 X0 X1 X2 X3
       grind)
    | exact resolve eq12 eq443323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443323
  have eq445677 : ∀ X0 X1 X2 X3 : G, (k X0 X0) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq444946 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444946
  have eq446747 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X2)) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq445677 (M.op X0 X1) X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445677
  have eq446765 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq446747 X0 X1 X2
       have j1 := eq432614 (M.op X0 X1) X0 X2 X1
       grind)
    | (have r₁ := eq446747 X1 X1 X2
       have r₂ := eq432614 (M.op X1 X1) X1 X2 x
       grind)
    | exact resolve eq446747 eq432614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432614 eq446747
  have eq447622 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (M.op X2 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18696 X0 X0 X1 X2 x
       have i₂ := eq446765 X0 X1 x
       grind)
    | exact superpose eq446765 eq18696
    | exact resolve eq18696 eq446765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18696 eq446765
  have eq449799 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (k (M.op X3 X4) (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq447622 X3 X4 X0
       have i₂ := eq2001 X1 X3 X0 X2
       grind)
    | exact superpose eq2001 eq447622
    | exact resolve eq447622 eq2001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2001 eq447622
  have eq463691 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq449799 X0 X1 X2 x x
       have i₂ := eq449799 X0 X3 X4 x x
       grind)
    | exact superpose eq449799 eq449799
    | exact resolve eq449799 eq449799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449799
  have eq467384 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 (M.op X1 X2)) X0) = (M.op X0 (M.op X4 X5)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq463691 X0 (M.op X1 X0) x X4 X5
       have i₂ := eq26 X0 X1 X2 x
       grind)
    | exact superpose eq26 eq463691
    | exact resolve eq463691 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq463691
  have eq473732 : ∀ X0 X1 X2 X3 X4 X5 : G, (k X0 (M.op X0 (M.op X1 X2))) = (M.op (M.op (M.op X3 X4) X0) X0) ∨ (M.op X0 (M.op (M.op X3 X4) (M.op X0 X5))) ≠ X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq133907 X0 (M.op X3 X4) X0 X5
       have i₂ := eq467384 X0 X3 X4 X1 X2
       grind)
    | exact superpose eq467384 eq133907
    | (have j0 := eq133907 X0 (M.op X3 X4) X0 X5
       grind)
    | (have r₁ := eq133907 (M.op (M.op X1 (M.op X2 X3)) (M.op X4 X5)) X1 X2 X3
       have r₂ := eq467384 (M.op X1 (M.op X2 X3)) X4 X5 X4 X5
       grind)
    | exact resolve eq133907 eq467384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133907 eq467384
  have eq475658 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X0) X0) = (k X0 (M.op X0 (M.op X1 X2))) ∨ (M.op X0 (M.op (M.op X3 X4) (M.op X0 X5))) ≠ X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq473732 X0 X1 X2 X3 X4 X5
       have i₂ := eq142 X3 X4 X0
       grind)
    | exact superpose eq142 eq473732
    | (have j0 := eq473732 X0 X1 X2 X3 X4 X5
       grind)
    | exact resolve eq473732 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473732
  have eq475876 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) X0) X0) ≠ X0 ∨ (M.op (M.op X4 X0) X0) = (k X0 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq475658 X0 X1 X2 X3 X4 x
       have i₂ := eq9 X0 (M.op X3 X4) (M.op X0 x)
       grind)
    | exact superpose eq9 eq475658
    | (have j0 := eq475658 X0 X1 X2 X3 X4 x
       grind)
    | exact resolve eq475658 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475658
  have eq475948 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X0) X0) ≠ X0 ∨ (M.op (M.op X4 X0) X0) = (k X0 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq475876 X0 X1 X2 x X4
       have i₂ := eq142 x X4 X0
       grind)
    | exact superpose eq142 eq475876
    | (have j0 := eq475876 X0 X1 X2 x X4
       grind)
    | exact resolve eq475876 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475876
  have eq475984 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X0) X0) = (k X0 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X4
    first
    | (have j0 := eq475948 X0 X1 X2 X4
       have j1 := eq432954 X4 X0 X0 (M.op X1 X2)
       grind)
    | (have r₁ := eq475948 X1 X1 X2 X0
       have r₂ := eq432954 X0 X1 X2 X4
       grind)
    | exact resolve eq475948 eq432954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432954 eq475948
  have eq477500 : ∀ X0 X1 : G, (σ (M.op (M.op X0 (τ X1)) (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) ∨ (M.op X0 (τ X1)) = (M.op (M.op X0 (τ X1)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq721 X0 X1 x
       have i₂ := eq9 (τ X0) X1 x
       grind)
    | exact superpose eq9 eq721
    | exact resolve eq721 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq477735 : ∀ X0 X1 : G, (σ (M.op (M.op X0 (τ X1)) (τ X1))) = (k (σ (M.op X0 (τ X1))) X1) := by
    intro X0 X1
    first
    | (have j0 := eq477500 X0 X1
       have j1 := eq617 X0 (τ X1) X1
       grind)
    | (have r₁ := eq477500 X0 x
       have r₂ := eq617 X0 (τ x) x
       grind)
    | exact resolve eq477500 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq477500
  have eq480718 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X0) = (M.op (k X0 (M.op X0 (M.op X1 X2))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq142 x X0 X0
       have i₂ := eq475984 X0 X1 X2 x
       grind)
    | exact superpose eq475984 eq142
    | exact resolve eq142 eq475984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq481331 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X0) X0) = (M.op (k X0 (M.op X0 (M.op X1 X2))) X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1615 (M.op x X0) X4 X0
       have i₂ := eq475984 X0 X1 X2 x
       grind)
    | exact superpose eq475984 eq1615
    | exact resolve eq1615 eq475984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615 eq475984
  have eq532542 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (k X0 (M.op X0 (M.op X1 X2))) X0) X0) = (k (M.op (k X0 (M.op X0 (M.op X1 X2))) X0) X0) ∨ (M.op (M.op X0 (M.op X3 X4)) X0) ≠ (M.op (k X0 (M.op X0 (M.op X1 X2))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq332 X0 X4 X2 X0
       have i₂ := eq481331 X0 X1 X2 X4
       grind)
    | exact superpose eq481331 eq332
    | exact resolve eq332 eq481331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq481331
  have eq534708 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X0) X0) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op (M.op X0 (M.op X3 X4)) X0) ≠ (M.op (k X0 (M.op X0 (M.op X1 X2))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq532542 X0 X1 X2 X3 X4
       have i₂ := eq480718 X0 X1 X2
       grind)
    | exact superpose eq480718 eq532542
    | (have j0 := eq532542 X0 X1 X2 X3 X4
       grind)
    | (have r₁ := eq532542 (M.op X3 X4) X1 X2 X3 X4
       have r₂ := eq480718 (M.op X3 X4) X1 X2
       grind)
    | exact resolve eq532542 eq480718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532542
  have eq535565 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) X0) = (k (M.op (M.op X0 X0) X0) X0) ∨ (M.op (M.op X0 (M.op X3 X4)) X0) ≠ (M.op (k X0 (M.op X0 (M.op X1 X2))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq534708 X0 X1 X2 X3 X4
       have i₂ := eq10169 X0 (M.op X0 X0)
       grind)
    | exact superpose eq10169 eq534708
    | (have j0 := eq534708 X0 X1 X2 X3 X4
       grind)
    | exact resolve eq534708 eq10169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534708
  have eq535985 : ∀ X0 X3 X4 : G, (M.op (M.op X0 X0) X0) ≠ (M.op (M.op X0 (M.op X3 X4)) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq535565 X0 x x X3 X4
       have i₂ := eq480718 X0 x x
       grind)
    | exact superpose eq480718 eq535565
    | (have j0 := eq535565 X0 x x X3 X4
       grind)
    | (have r₁ := eq535565 (M.op X3 X4) x x X3 X4
       have r₂ := eq480718 (M.op X3 X4) x x
       grind)
    | exact resolve eq535565 eq480718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480718 eq535565
  have eq536223 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op (M.op X0 X0) X0) X0) := by
    intro X0
    first
    | (have j0 := eq535985 X0 x x
       grind)
    | (have r₁ := eq535985 x X0 x
       have r₂ := eq11709 X0 x x x
       grind)
    | (have r₁ := eq535985 (M.op X0 x) X0 x
       have r₂ := eq11709 X0 (M.op X0 x) (M.op X0 x) x
       grind)
    | exact resolve eq535985 eq11709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11709 eq535985
  have eq536605 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op (M.op X0 X1) X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq536223 X0
       have i₂ := eq10169 X0 X0
       grind)
    | (have i₁ := eq536223 X0
       have i₂ := eq10169 X0 X1
       grind)
    | exact superpose eq10169 eq536223
    | exact resolve eq536223 eq10169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10169 eq536223
  have eq917363 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X0) X0)) = (k (σ (M.op X1 X0)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq477735 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq477735
    | exact resolve eq477735 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477735
  have eq917725 : ∀ X0 X1 : G, (σ (k (M.op X1 X0) X0)) = (σ (M.op (M.op X1 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq917363 X0 X1
       have i₂ := eq15 (M.op X1 X0) X0
       grind)
    | exact superpose eq15 eq917363
    | exact resolve eq917363 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917363
  have eq918277 : (σ (M.op x y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq917725 y x
       have i₂ := eq831
       grind)
    | exact superpose eq831 eq917725
    | exact resolve eq917725 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq917725
  have eq918592 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq918277
       have r₂ := eq576
       grind)
    | exact resolve eq918277 eq576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq918277
  have eq918835 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq918592
       grind)
    | exact superpose eq918592 eq16
    | exact resolve eq16 eq918592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919317 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq536605 (σ x) (σ y)
       have i₂ := eq918592
       grind)
    | exact superpose eq918592 eq536605
    | exact resolve eq536605 eq918592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536605
  have eq919437 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq919317
       have i₂ := eq918592
       grind)
    | exact superpose eq918592 eq919317
    | exact resolve eq919317 eq918592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918592 eq919317
  have eq919571 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq919437
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq919437
    | exact resolve eq919437 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919437
  have eq919707 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq743 y x
       have i₂ := eq919571
       grind)
    | exact superpose eq919571 eq743
    | (have j0 := eq743 y x
       grind)
    | exact resolve eq743 eq919571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq919571
  have eq919919 : x = (M.op x y) := by
    first
    | (have r₁ := eq919707
       have r₂ := eq918835
       grind)
    | exact resolve eq919707 eq918835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919707
  have eq920025 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq918835
       have i₂ := eq919919
       grind)
    | exact superpose eq919919 eq918835
    | exact resolve eq918835 eq919919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918835 eq919919
  have eq920584 : False := by grind
  exact eq920584

/-- `Equation4652`: `(x ◇ y) ◇ x = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxx_pyx_Equation4652 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4652 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4652.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X3) X3) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) y) := by
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
  have eq189 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ x) (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op X0 X1) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 (M.op X2 x) X2
       have i₂ := eq16 X2 x X0 X1
       grind)
    | (have i₁ := eq175 (M.op X2 x) x
       have i₂ := eq16 X0 X1 X2 x
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) X1) := by
    intro X1
    first
    | (have i₁ := eq175 (M.op x X1) X1
       have i₂ := eq175 x X1
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x x
       have i₂ := eq175 x x
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op (M.op x y) x) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) X1 X2 X3
       have i₂ := eq175 X0 X1
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq201 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op x y) x) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1 x x
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq200
    | exact resolve eq200 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq204 : ∀ X2 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X2) := by
    intro X2
    first
    | (have i₁ := eq192 x x X2
       have i₂ := eq176 x x
       grind)
    | exact superpose eq176 eq192
    | exact resolve eq192 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq192
  have eq205 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq193 eq201
    | exact resolve eq201 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq371 : (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq193 eq189
    | exact resolve eq189 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq627 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1219 : ∀ X0 : G, (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq193 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq28 x (M.op (M.op x y) x)
       have r₂ := eq193 x
       grind)
    | exact resolve eq28 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1227 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have j0 := eq1219 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq1261 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq1263 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1430 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) x)) = X0 ∨ (k X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq1227 X0
       grind)
    | exact superpose eq1227 eq11
    | exact resolve eq11 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1445 : ∀ X0 X1 : G, (k X0 (M.op (M.op x y) x)) ≠ X1 ∨ (k X0 X1) = (k X0 (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq1227 X0
       grind)
    | exact superpose eq1227 eq13
    | (have r₁ := eq13 X0 (k X0 (M.op (M.op x y) x))
       have r₂ := eq1227 X0
       grind)
    | exact resolve eq13 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1457 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq1430 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1471 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1457 X0
       have j1 := eq1445 X0 X0
       grind)
    | (have r₁ := eq1457 X0
       have r₂ := eq1445 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1457 (M.op (M.op x y) x)
       have r₂ := eq1445 (M.op (M.op x y) x) (k (M.op (M.op x y) x) (M.op (M.op x y) x))
       grind)
    | (have r₁ := eq1457 x
       have r₂ := eq1445 x x
       grind)
    | exact resolve eq1457 eq1445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445 eq1457
  have eq1481 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1227 (M.op sF0 x)
       have i₂ := eq1471 (M.op sF0 x)
       grind)
    | exact superpose eq1471 eq1227
    | exact resolve eq1227 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1493 : ∀ X0 : G, (τ (k (σ X0) (M.op (M.op x y) x))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq627 X0 (σ X0)
       have i₂ := eq1471 (σ X0)
       grind)
    | (have i₁ := eq627 X0 (M.op (M.op x y) x)
       have i₂ := eq1471 (σ X0)
       grind)
    | exact superpose eq1471 eq627
    | exact resolve eq627 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq1497 : ∀ X0 : G, (k X0 X0) = (τ (k (σ X0) (M.op (M.op x y) x))) := by
    intro X0
    first
    | (have i₁ := eq1493 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1493
    | exact resolve eq1493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1510 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (M.op x y) x))) := by
    intro X0
    first
    | (have i₁ := eq1497 X0
       have i₂ := eq627 X0 (M.op sF0 x)
       grind)
    | exact superpose eq627 eq1497
    | exact resolve eq1497 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq1551 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq198 X0 X0
       have i₂ := eq1481 X0
       grind)
    | exact superpose eq1481 eq198
    | exact resolve eq198 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq1589 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1551 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1551
    | exact resolve eq1551 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3123 : (M.op (M.op x y) x) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq371 eq1589
    | exact resolve eq1589 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3207 : (M.op (M.op x y) x) = (k (σ (M.op (M.op x y) x)) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq3123
       have i₂ := eq1227 (σ (M.op sF0 x))
       grind)
    | exact superpose eq1227 eq3123
    | exact resolve eq3123 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq3123
  have eq4172 : (τ (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) (τ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq3207 eq627
    | exact resolve eq627 eq3207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627 eq3207
  have eq4179 : (k (M.op (M.op x y) x) (M.op (M.op x y) x)) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1510 eq4172
    | exact resolve eq4172 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510 eq4172
  have eq4182 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq371 eq4179
    | exact resolve eq4179 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq4179
  have eq4199 : (M.op (M.op x y) x) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq4182 eq14
    | exact resolve eq14 eq4182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4857 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1261
       grind)
    | exact superpose eq1261 eq40
    | exact resolve eq40 eq1261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1261
  have eq4859 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq4857
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4857
    | exact resolve eq4857 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4857
  have eq4861 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq4859
    | exact resolve eq4859 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4859
  have eq4863 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4861
       have i₂ := eq1481 y
       grind)
    | exact superpose eq1481 eq4861
    | exact resolve eq4861 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4861
  have eq4875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4863 eq1263
    | exact resolve eq1263 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq4863
  have eq4884 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4875
       have r₂ := eq27
       grind)
    | exact resolve eq4875 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4875
  have eq4888 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4884
       have i₂ := eq1481 sF3
       grind)
    | exact superpose eq1481 eq4884
    | exact resolve eq4884 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4884
  have eq4890 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4888 eq116
    | exact resolve eq116 eq4888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq4888
  have eq4906 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq4890
    | exact resolve eq4890 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4890
  have eq4907 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4906
  have eq4917 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1551 y
       have i₂ := eq4907
       grind)
    | exact superpose eq4907 eq1551
    | exact resolve eq1551 eq4907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq4920 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1589 y
       have i₂ := eq4907
       grind)
    | exact superpose eq4907 eq1589
    | exact resolve eq1589 eq4907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4907
  have eq4924 : (M.op (M.op x y) x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4920
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4920
    | exact resolve eq4920 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4920
  have eq4925 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4917
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4917
    | exact resolve eq4917 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4917
  have eq4929 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4924
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4924
    | exact resolve eq4924 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4924
  have eq4933 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4929
    | exact resolve eq4929 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4929
  have eq4934 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4925 eq4933
    | exact resolve eq4933 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933
  have eq4937 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4934 eq191
    | exact resolve eq191 eq4934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4941 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq4946 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4937
    | exact resolve eq4937 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4937
  have eq4949 : (σ x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4934 eq4946
    | exact resolve eq4946 eq4934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4934 eq4946
  have eq5637 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4925 eq4199
    | exact resolve eq4199 eq4925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4199 eq4925
  have eq5669 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5637
    | exact resolve eq5637 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5637
  have eq5806 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5669 eq191
    | exact resolve eq191 eq5669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq5814 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq5806
    | exact resolve eq5806 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5806
  have eq5817 : (σ x) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5669 eq5814
    | exact resolve eq5814 eq5669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5814
  have eq6163 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4949 eq193
    | exact resolve eq193 eq4949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq6206 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4949 eq4182
    | exact resolve eq4182 eq4949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4949
  have eq6247 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq6206
    | exact resolve eq6206 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6206
  have eq6406 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6247 eq27
    | exact resolve eq27 eq6247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6247
  have eq7172 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5817 eq4182
    | exact resolve eq4182 eq5817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4182 eq5817
  have eq7214 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq7172
    | exact resolve eq7172 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7172
  have eq7264 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7214
       have r₂ := eq6406
       grind)
    | exact resolve eq7214 eq6406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6406 eq7214
  have eq7327 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7264
       grind)
    | exact superpose eq7264 eq18
    | exact resolve eq18 eq7264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7385 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq7264
  have eq7510 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7327 eq6163
    | exact resolve eq6163 eq7327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6163 eq7327
  have eq7529 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7510
  have eq7546 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7529
       have r₂ := eq4941
       grind)
    | exact resolve eq7529 eq4941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4941 eq7529
  have eq7562 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7546 eq27
    | exact resolve eq27 eq7546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7568 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7546 eq5669
    | exact resolve eq5669 eq7546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5669 eq7546
  have eq7569 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq7568
  have eq7572 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7569
       have r₂ := eq7385
       grind)
    | exact resolve eq7569 eq7385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7385 eq7569
  have eq7576 : x = (M.op x y) := by
    first
    | (have r₁ := eq7572
       have r₂ := eq7562
       grind)
    | exact resolve eq7572 eq7562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7562 eq7572
  have eq7579 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7576
       grind)
    | exact superpose eq7576 eq18
    | exact resolve eq18 eq7576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7580 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq7576
       grind)
    | exact superpose eq7576 eq22
    | exact resolve eq22 eq7576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq7806 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7580 eq20
    | exact resolve eq20 eq7580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7580
  have eq7944 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7579 eq181
    | exact resolve eq181 eq7579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq7579
  have eq7960 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq7944
       have i₂ := eq1481 sF0
       grind)
    | exact superpose eq1481 eq7944
    | exact resolve eq7944 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7944
  have eq7980 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7960 eq38
    | exact resolve eq38 eq7960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq7987 : (M.op (M.op x y) x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7960 eq1589
    | exact resolve eq1589 eq7960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq7998 : (M.op (M.op x y) x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7987
       have i₂ := eq1481 (σ sF0)
       grind)
    | exact superpose eq1481 eq7987
    | exact resolve eq7987 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7987
  have eq8002 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq7980
    | exact resolve eq7980 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7980
  have eq8004 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq7998
       have i₂ := eq10 sF0 sF0
       grind)
    | exact superpose eq10 eq7998
    | exact resolve eq7998 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7998
  have eq8007 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq7806 eq8002
    | exact resolve eq8002 eq7806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8002
  have eq8009 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq8004
       have i₂ := eq7576
       grind)
    | exact superpose eq7576 eq8004
    | exact resolve eq8004 eq7576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8004
  have eq8012 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq8009
       have i₂ := eq1481 sF0
       grind)
    | exact superpose eq1481 eq8009
    | exact resolve eq8009 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009
  have eq8013 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42 eq8012
    | exact resolve eq8012 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq8012
  have eq8014 : (k (σ (M.op x y)) (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7806 eq8013
    | exact resolve eq8013 eq7806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8013
  have eq8015 : (M.op x y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq7960 eq8014
    | exact resolve eq8014 eq7960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8014
  have eq8016 : (M.op x y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq8015
    | exact resolve eq8015 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8015
  have eq8017 : (M.op x y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq7806 eq8016
    | exact resolve eq8016 eq7806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7806 eq8016
  have eq8069 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq8017 eq8007
    | exact resolve eq8007 eq8017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8007
  have eq8071 : (k x x) = (τ (M.op x y)) := by
    first
    | exact superpose eq8017 eq98
    | exact resolve eq98 eq8017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq8017
  have eq8092 : (k (M.op x y) (M.op x y)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq8071
       have i₂ := eq7576
       grind)
    | exact superpose eq7576 eq8071
    | exact resolve eq8071 eq7576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8071
  have eq8097 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq7960 eq8092
    | exact resolve eq8092 eq7960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8092
  have eq8107 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq8069 eq26
    | exact resolve eq26 eq8069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq8118 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq8069 eq204
    | exact resolve eq204 eq8069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq8119 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq8069 eq205
    | exact resolve eq205 eq8069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq8069
  have eq8148 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq8119
       have i₂ := eq7576
       grind)
    | exact superpose eq7576 eq8119
    | exact resolve eq8119 eq7576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8119
  have eq8149 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq8118 X0
       have i₂ := eq7576
       grind)
    | exact superpose eq7576 eq8118
    | exact resolve eq8118 eq7576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7576 eq8118
  have eq8163 : (k (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq8148
       have i₂ := eq1481 sF0
       grind)
    | exact superpose eq1481 eq8148
    | exact resolve eq8148 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8148
  have eq8164 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq8149 X0
       have i₂ := eq1481 sF0
       grind)
    | exact superpose eq1481 eq8149
    | exact resolve eq8149 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481 eq8149
  have eq8175 : (M.op x y) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq7960 eq8163
    | exact resolve eq8163 eq7960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8163
  have eq8176 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq7960 eq8164
    | exact resolve eq8164 eq7960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7960 eq8164
  have eq8183 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq8175 eq8176
    | exact resolve eq8176 eq8175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8175 eq8176
  have eq8195 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq8097 eq14
    | exact resolve eq14 eq8097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8097
  have eq8211 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq8195 eq20
    | exact resolve eq20 eq8195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8195
  have eq8461 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8183 eq8107
    | exact resolve eq8107 eq8183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8107 eq8183
  have eq8651 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq8461 eq27
    | exact resolve eq27 eq8461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8461
  have eq8664 : False := by grind
  exact eq8664

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_pxx_pxy_Equation58 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq13 X1 X1
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
  have eq36 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X0) X0 x
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq37 eq16
    | exact resolve eq16 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq40 eq16
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq59 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq62 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq63 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq64 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq15
    | exact resolve eq15 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq67 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq67
    | exact resolve eq67 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq67 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq67
    | (have j0 := eq67 x
       grind)
    | exact resolve eq67 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq130 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq70 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq70
    | exact resolve eq70 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq70 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq70
    | (have j0 := eq70 y
       grind)
    | exact resolve eq70 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq158 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (M.op X1 (M.op X2 X0))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq28
    | (have j0 := eq28 X0 (M.op X1 (M.op X2 X0))
       grind)
    | (have r₁ := eq28 X0 (M.op X1 (M.op X2 X0))
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq38 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | (have r₁ := eq28 (M.op x y) y
       have r₂ := eq38
       grind)
    | exact resolve eq28 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq165 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq42 eq28
    | (have j0 := eq28 (M.op (σ x) (σ y)) (σ y)
       grind)
    | (have r₁ := eq28 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq42
       grind)
    | exact resolve eq28 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq166 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (σ y)) := by grind
  clear eq165
  have eq168 : (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq162
  have eq171 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq158 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158
  have eq173 : (M.op x y) ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq176
       have i₂ := eq178 sF2
       grind)
    | exact superpose eq178 eq176
    | exact resolve eq176 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq180 : (M.op x y) ≠ (k x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq173
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq173
    | exact resolve eq173 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq181 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq179
       have i₂ := eq178 sF2
       grind)
    | exact superpose eq178 eq179
    | exact resolve eq179 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq182 : (M.op x y) ≠ (k x x) ∨ (k x x) = (k x y) := by
    first
    | (have i₁ := eq180
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq180
    | exact resolve eq180 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq184 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq36 X0 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq36
    | exact resolve eq36 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq185 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 X0
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : y = (M.op y (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq37 sF0
       have i₂ := eq178 sF0
       grind)
    | exact superpose eq178 eq37
    | exact resolve eq37 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (σ y) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq40 sF4
       have i₂ := eq178 sF4
       grind)
    | exact superpose eq178 eq40
    | exact resolve eq40 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : y ≠ y ∨ (M.op y y) = (k y (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq187 eq28
    | (have j0 := eq28 y (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq28 y (k (M.op x y) (M.op x y))
       have r₂ := eq187
       grind)
    | exact resolve eq28 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq193 : (M.op y y) = (k y (k (M.op x y) (M.op x y))) := by grind
  clear eq190
  have eq194 : (k y y) = (k y (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq193
       have i₂ := eq178 y
       grind)
    | exact superpose eq178 eq193
    | exact resolve eq193 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq198 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq188 eq28
    | (have j0 := eq28 (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq28 (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       have r₂ := eq188
       grind)
    | exact resolve eq28 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq188
  have eq201 : (M.op (σ y) (σ y)) = (k (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by grind
  clear eq198
  have eq202 : (k (σ y) (σ y)) = (k (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq201
       have i₂ := eq178 sF3
       grind)
    | exact superpose eq178 eq201
    | exact resolve eq201 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq209 : (k (M.op (σ x) (σ y)) (σ y)) ≠ (k (M.op (σ x) (σ y)) (σ y)) ∨ (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq166 eq13
    | exact resolve eq13 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166
  have eq213 : (k (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by grind
  clear eq209
  have eq218 : (k (M.op x y) y) ≠ (k (M.op x y) y) ∨ (k (M.op x y) y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq168 eq13
    | exact resolve eq13 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq222 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq218
  have eq236 : (k (σ (M.op x y)) (σ y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq222 eq63
    | exact resolve eq63 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq237 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq64 eq236
    | exact resolve eq236 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq239 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq237
    | exact resolve eq237 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq264 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq95 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq95
    | exact resolve eq95 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq301 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq184 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq184
    | exact resolve eq184 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq372 : (σ (k y y)) = (k (σ y) (σ (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq194 eq59
    | exact resolve eq59 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq194
  have eq373 : (σ (k y y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq64 eq372
    | exact resolve eq372 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq372
  have eq374 : (σ (k y y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq373
    | exact resolve eq373 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq375 : (σ (k y y)) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq239 eq374
    | exact resolve eq374 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq376 : (k (σ y) (σ y)) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq375
       have i₂ := eq63 y
       grind)
    | exact superpose eq63 eq375
    | exact resolve eq375 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq377 : (k (σ y) (σ y)) = (k (σ y) (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq376
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq376
    | exact resolve eq376 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq376
  have eq379 : (τ (k (σ y) (σ y))) = (k y (τ (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq202 eq130
    | exact resolve eq130 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq380 : (τ (k (σ y) (σ y))) = (k y (τ (k (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq213 eq379
    | exact resolve eq379 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq379
  have eq381 : (τ (k (σ y) (σ y))) = (k y (k (τ (M.op (σ x) (σ y))) y)) := by
    first
    | exact superpose eq264 eq380
    | exact resolve eq380 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq380
  have eq382 : (k y y) = (k y (k (τ (M.op (σ x) (σ y))) y)) := by
    first
    | exact superpose eq138 eq381
    | exact resolve eq381 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq459 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq486 X0 X1
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq486
    | (have j0 := eq486 X0 X1
       grind)
    | (have r₁ := eq486 X0 X0
       have r₂ := eq178 X0
       grind)
    | exact resolve eq486 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq500 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq460
       have i₂ := eq178 sF2
       grind)
    | exact superpose eq178 eq460
    | exact resolve eq460 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq501 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq459
       have i₂ := eq178 x
       grind)
    | exact superpose eq178 eq459
    | exact resolve eq459 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459
  have eq502 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 X1
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq487
    | (have j0 := eq487 X0 X1
       grind)
    | exact resolve eq487 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq1008 : ∀ X0 X1 : G, (k x (τ (M.op X0 (M.op X1 (σ x))))) = (τ (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq113 (M.op X1 (M.op x sF2))
       have i₂ := eq171 sF2 X1 x
       grind)
    | exact superpose eq171 eq113
    | exact resolve eq113 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1009 : ∀ X0 X1 : G, (τ (M.op (σ y) (σ y))) = (k y (τ (M.op X0 (M.op X1 (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq130 (M.op X1 (M.op x sF3))
       have i₂ := eq171 sF3 X1 x
       grind)
    | exact superpose eq171 eq130
    | exact resolve eq130 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq171
  have eq1010 : ∀ X0 X1 : G, (τ (k (σ y) (σ y))) = (k y (τ (M.op X0 (M.op X1 (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1009 X0 X1
       have i₂ := eq178 sF3
       grind)
    | exact superpose eq178 eq1009
    | exact resolve eq1009 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1009
  have eq1011 : ∀ X0 X1 : G, (τ (k (σ x) (σ x))) = (k x (τ (M.op X0 (M.op X1 (σ x))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1008 X0 X1
       have i₂ := eq178 sF2
       grind)
    | exact superpose eq178 eq1008
    | exact resolve eq1008 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq1044 : ∀ X0 X1 : G, (k y y) = (k y (τ (M.op X0 (M.op X1 (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq138 eq1010
    | exact resolve eq1010 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq1010
  have eq1045 : ∀ X0 X1 : G, (k x x) = (k x (τ (M.op X0 (M.op X1 (σ x))))) := by
    intro X0 X1
    first
    | exact superpose eq120 eq1011
    | exact resolve eq1011 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq1011
  have eq2306 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq501
       grind)
    | exact superpose eq501 eq63
    | exact resolve eq63 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2309 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2306
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2306
    | exact resolve eq2306 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2306
  have eq2311 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2309
    | exact resolve eq2309 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309
  have eq3908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2311 eq500
    | exact resolve eq500 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3920 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3908
       have r₂ := eq27
       grind)
    | exact resolve eq3908 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908
  have eq3927 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3920 eq181
    | (have r₁ := eq181
       have r₂ := eq3920
       grind)
    | exact resolve eq181 eq3920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq3920
  have eq3946 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq3927
  have eq3953 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2311 eq3946
    | exact resolve eq3946 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2311 eq3946
  have eq3956 : (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3953
       have r₂ := eq27
       grind)
    | exact resolve eq3953 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953
  have eq3958 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq182
       have i₂ := eq3956
       grind)
    | exact superpose eq3956 eq182
    | (have r₁ := eq182
       have r₂ := eq3956
       grind)
    | exact resolve eq182 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq3960 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62 x
       have i₂ := eq3956
       grind)
    | exact superpose eq3956 eq62
    | exact resolve eq62 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq3956
  have eq3976 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3958
  have eq3981 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3960
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3960
    | exact resolve eq3960 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3960
  have eq3986 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3981
    | exact resolve eq3981 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3981
  have eq4018 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63 x
       have i₂ := eq3976
       grind)
    | exact superpose eq3976 eq63
    | exact resolve eq63 eq3976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq3976
  have eq4023 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4018
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4018
    | exact resolve eq4018 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4018
  have eq4026 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4023
    | exact resolve eq4023 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4023
  have eq4096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4026 eq500
    | exact resolve eq500 eq4026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4026
  have eq4103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4096
  have eq4110 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4103
       have r₂ := eq27
       grind)
    | exact resolve eq4103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4103
  have eq4117 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3986 eq4110
    | exact resolve eq4110 eq3986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3986 eq4110
  have eq4122 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4117
       have r₂ := eq27
       grind)
    | exact resolve eq4117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4117
  have eq4127 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4122 eq40
    | exact resolve eq40 eq4122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4144 : (k y y) = (k y (k (τ (σ x)) y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4122 eq382
    | exact resolve eq382 eq4122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq4122
  have eq4161 : (k y y) = (k y (k x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq4144
    | exact resolve eq4144 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4144
  have eq4176 : (k x x) = (k x (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4127 eq1045
    | exact resolve eq1045 eq4127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq4204 : (k x x) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq4176
    | exact resolve eq4176 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4176
  have eq4272 : (M.op x y) = (k x x) ∨ (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq501
       have i₂ := eq4204
       grind)
    | exact superpose eq4204 eq501
    | exact resolve eq501 eq4204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501
  have eq4278 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq4272
  have eq4295 : ∀ X0 : G, x = (M.op x (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq185 x X0
       have i₂ := eq4278
       grind)
    | exact superpose eq4278 eq185
    | exact resolve eq185 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4296 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq301 x
       have i₂ := eq4278
       grind)
    | exact superpose eq4278 eq301
    | exact resolve eq301 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301
  have eq4313 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4296
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4296
    | exact resolve eq4296 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296
  have eq4318 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4313
    | exact resolve eq4313 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4313
  have eq4366 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4318 eq4127
    | exact resolve eq4127 eq4318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127 eq4318
  have eq4382 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq4366
  have eq4460 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4382 eq16
    | exact resolve eq16 eq4382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4382
  have eq5071 : (k y y) = (k y (τ (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4460 eq1044
    | exact resolve eq1044 eq4460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044 eq4460
  have eq5099 : (k y y) = (k y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq5071
    | exact resolve eq5071 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5071
  have eq5273 : ∀ X0 : G, y = (M.op y (M.op X0 (k y (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq185 y X0
       have i₂ := eq5099
       grind)
    | exact superpose eq5099 eq185
    | exact resolve eq185 eq5099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5666 : (k y y) ≠ (k y y) ∨ (k y y) = (M.op y (k x y)) ∨ y = (M.op y (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq502 y (k x y)
       have i₂ := eq4161
       grind)
    | exact superpose eq4161 eq502
    | (have j0 := eq502 y (k x y)
       grind)
    | (have r₁ := eq502 y (k x y)
       have r₂ := eq4161
       grind)
    | exact resolve eq502 eq4161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4161
  have eq5668 : (k y y) = (M.op y (k x y)) ∨ y = (M.op y (k x y)) ∨ x = (M.op x y) := by grind
  clear eq5666
  have eq5674 : (k y y) = (M.op y (k x x)) ∨ y = (M.op y (k x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4204 eq5668
    | exact resolve eq5668 eq4204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5668
  have eq5679 : (k y y) = (M.op y (k x x)) ∨ y = (M.op y (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4204 eq5674
    | exact resolve eq5674 eq4204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204 eq5674
  have eq5683 : (k y y) = (M.op y (M.op x y)) ∨ y = (M.op y (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4278 eq5679
    | exact resolve eq5679 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5679
  have eq5687 : (k y y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4278 eq5683
    | exact resolve eq5683 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278 eq5683
  have eq5691 : (k y (M.op x y)) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5099 eq5687
    | exact resolve eq5687 eq5099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5687
  have eq8375 : y = (M.op y (k y (M.op x y))) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5691 eq37
    | exact resolve eq37 eq5691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq8404 : y ≠ (k y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5691
  have eq8441 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8375 eq5273
    | exact resolve eq5273 eq8375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273 eq8375
  have eq8458 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq8441
  have eq8468 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq8458
       have i₂ := eq178 y
       grind)
    | exact superpose eq178 eq8458
    | exact resolve eq8458 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8458
  have eq8476 : y = (k y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq5099 eq8468
    | exact resolve eq8468 eq5099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5099 eq8468
  have eq8478 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8476
       have r₂ := eq8404
       grind)
    | exact resolve eq8476 eq8404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8404 eq8476
  have eq8492 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8478 eq4295
    | exact resolve eq4295 eq8478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4295 eq8478
  have eq8514 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8492
  have eq8524 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8514
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8514
    | exact resolve eq8514 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq8514
  have eq8525 : x = (M.op x y) := by grind
  clear eq8524
  have eq8532 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq8525
       grind)
    | exact superpose eq8525 eq22
    | exact resolve eq22 eq8525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8525
  have eq8546 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8532 eq20
    | exact resolve eq20 eq8532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8532
  have eq8632 : (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq8546 eq239
    | exact resolve eq239 eq8546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq8636 : (k (σ y) (σ y)) = (k (σ y) (k (σ x) (σ y))) := by
    first
    | exact superpose eq8546 eq377
    | exact resolve eq377 eq8546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq8737 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8632 eq500
    | exact resolve eq500 eq8632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq8756 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8737
  have eq8788 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8756 eq185
    | exact resolve eq185 eq8756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9473 : (k (σ y) (σ y)) = (k (σ y) (k (σ x) (σ x))) := by
    first
    | exact superpose eq8632 eq8636
    | exact resolve eq8636 eq8632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8632 eq8636
  have eq9536 : (k (σ y) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8756 eq9473
    | exact resolve eq9473 eq8756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8756 eq9473
  have eq10081 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9536 eq502
    | (have j0 := eq502 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq502 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq9536
       grind)
    | exact resolve eq502 eq9536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502 eq9536
  have eq10083 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10081
  have eq16574 : (σ y) = (M.op (σ y) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10083 eq40
    | exact resolve eq40 eq10083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq16600 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10083
  have eq17269 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16574 eq185
    | exact resolve eq185 eq16574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq16574
  have eq17296 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17269
       have i₂ := eq178 sF3
       grind)
    | exact superpose eq178 eq17269
    | exact resolve eq17269 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq17269
  have eq17302 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17296
       have r₂ := eq16600
       grind)
    | exact resolve eq17296 eq16600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16600 eq17296
  have eq17312 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17302 eq8788
    | exact resolve eq8788 eq17302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8788 eq17302
  have eq17336 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17312
  have eq17348 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17336
    | exact resolve eq17336 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq17336
  have eq17349 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17348
  have eq17356 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq17349 eq27
    | exact resolve eq27 eq17349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq17349
  have eq17398 : False := by grind
  exact eq17398

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq18
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (M.op (τ X1) (τ X1)) = X0 := by
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
  have eq87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq211 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq212 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq215 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq211 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq218 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq215 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq215
    | (have j0 := eq215 X0
       grind)
    | exact resolve eq215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq423 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) (σ (τ X0))) = (σ (k (τ (k X0 X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq218 (τ X0)
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq218
    | (have j0 := eq218 (τ X0)
       grind)
    | exact resolve eq218 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq443 : ∀ X0 : G, (M.op (σ (τ (k X0 X0))) (σ (τ X0))) = (k (σ (τ (k X0 X0))) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq423 X0
       have i₂ := eq19 X0 (τ (k X0 X0))
       grind)
    | exact superpose eq19 eq423
    | (have j0 := eq423 X0
       grind)
    | exact resolve eq423 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq449 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq443 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq443
    | (have j0 := eq443 X0
       grind)
    | exact resolve eq443 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq453 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq449 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq449
    | (have j0 := eq449 X0
       grind)
    | exact resolve eq449 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq457 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq453 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq453
    | (have j0 := eq453 X0
       grind)
    | exact resolve eq453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq568 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq603 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq568
    | (have j0 := eq568 X0 X1
       grind)
    | exact resolve eq568 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq643 : ∀ X0 : G, (k (σ (k (τ X0) (τ X0))) X0) = (σ (M.op (k (τ X0) (τ X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (k (τ X0) (τ X0))
       have i₂ := eq457 (τ X0)
       grind)
    | exact superpose eq457 eq19
    | (have j1 := eq457 (τ X0)
       grind)
    | exact resolve eq19 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq457
  have eq649 : ∀ X0 : G, (k (σ (τ (k X0 X0))) X0) = (σ (M.op (τ (k X0 X0)) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq643 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq643
    | (have j0 := eq643 X0
       grind)
    | exact resolve eq643 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq665 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = (σ (M.op (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq649 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq649
    | (have j0 := eq649 X0
       grind)
    | exact resolve eq649 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq968 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq603 (τ X1) (τ X0)
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq603
    | (have j0 := eq603 (τ X1) (τ X0)
       grind)
    | exact resolve eq603 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq1021 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq968 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq968
    | (have j0 := eq968 X0 X1
       grind)
    | exact resolve eq968 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq6124 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (k (k X0 X0) X0) = (σ (M.op (τ (k X0 X0)) (τ X0))) := by
    intro X0
    grind
  clear eq665
  have eq6143 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k (k X0 X0) X0) = (σ (M.op (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6124 X0
       have i₂ := eq35 X0 X0
       grind)
    | exact superpose eq35 eq6124
    | (have j0 := eq6124 X0
       grind)
    | exact resolve eq6124 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6124
  have eq176812 : ∀ X0 : G, (k (σ (τ (k X0 X0))) X0) = (σ (M.op (τ (k X0 X0)) (τ X0))) ∨ (k (k X0 X0) X0) = (σ (M.op (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq6143 X0
       grind)
    | exact superpose eq6143 eq34
    | (have j1 := eq6143 X0
       grind)
    | exact resolve eq34 eq6143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6143
  have eq177116 : ∀ X0 : G, (k (k X0 X0) X0) = (σ (M.op (τ (k X0 X0)) (τ X0))) ∨ (k (k X0 X0) X0) = (σ (M.op (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq176812 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq176812
    | (have j0 := eq176812 X0
       grind)
    | exact resolve eq176812 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176812
  have eq177117 : ∀ X0 : G, (k (k X0 X0) X0) = (σ (M.op (τ (k X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq177116 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177116
  have eq177605 : ∀ X0 : G, (k (k (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 (τ (σ X0))) (τ (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq177117 (σ X0)
       have i₂ := eq31 X0 (σ X0)
       grind)
    | exact superpose eq31 eq177117
    | exact resolve eq177117 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177117
  have eq178011 : ∀ X0 : G, (k (k (σ X0) (σ X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq177605 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq177605
    | exact resolve eq177605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177605
  have eq178077 : ∀ X0 : G, (σ (k (k (τ (σ X0)) X0) X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq178011 X0
       have i₂ := eq24 (σ X0) X0 X0
       grind)
    | exact superpose eq24 eq178011
    | exact resolve eq178011 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq178011
  have eq178099 : ∀ X0 : G, (σ (k (k X0 X0) X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq178077 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq178077
    | exact resolve eq178077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178077
  have eq178234 : ∀ X0 : G, (k (k X0 X0) X0) = (τ (σ (M.op (k X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k (k X0 X0) X0)
       have i₂ := eq178099 X0
       grind)
    | exact superpose eq178099 eq10
    | exact resolve eq10 eq178099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178567 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq178234 X0
       have i₂ := eq10 (M.op (k X0 X0) X0)
       grind)
    | exact superpose eq10 eq178234
    | exact resolve eq178234 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178234
  have eq179033 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (k (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq178567 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq178567
    | exact resolve eq178567 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178567
  have eq179309 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq179033 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq179033
    | exact resolve eq179033 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179033
  have eq179402 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (σ (M.op (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq179309 X0
       have i₂ := eq178099 X0
       grind)
    | exact superpose eq178099 eq179309
    | exact resolve eq179309 eq178099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178099 eq179309
  have eq276713 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq1021 X0 X1
       grind)
    | exact superpose eq1021 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq1021 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq1021 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X0)
       have r₂ := eq1021 X0 X0
       grind)
    | exact resolve eq13 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276733 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq1021 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq276734 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq276733 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276733
  have eq276735 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq276713 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276713
  have eq276736 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq276735 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276735
  have eq276749 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (M.op (τ X1) (τ X1)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq276736 X0 X1
       have i₂ := eq35 X1 X0
       grind)
    | exact superpose eq35 eq276736
    | (have j0 := eq276736 X0 X1
       grind)
    | exact resolve eq276736 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq276736
  have eq276976 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq276734 X0
       grind)
    | exact superpose eq276734 eq34
    | (have j1 := eq276734 X0
       grind)
    | exact resolve eq34 eq276734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq276734
  have eq277115 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq276976 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq276976
    | (have j0 := eq276976 X0
       grind)
    | exact resolve eq276976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276976
  have eq277116 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq277115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277115
  have eq277212 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq277116 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277116
    | exact resolve eq277116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277406 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq277116 X0
       grind)
    | exact superpose eq277116 eq10
    | exact resolve eq10 eq277116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277116
  have eq277953 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq277212 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq277212
    | exact resolve eq277212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277212
  have eq278718 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq277953 X0
       grind)
    | exact superpose eq277953 eq10
    | exact resolve eq10 eq277953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279215 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq278718 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq278718
    | exact resolve eq278718 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278718
  have eq279945 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq179402 X0
       have i₂ := eq279215 X0
       grind)
    | exact superpose eq279215 eq179402
    | exact resolve eq179402 eq279215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179402
  have eq280085 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq279215 (σ X0)
       grind)
    | exact superpose eq279215 eq15
    | exact resolve eq15 eq279215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280332 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280085 X0
       have i₂ := eq277953 X0
       grind)
    | exact superpose eq277953 eq280085
    | exact resolve eq280085 eq277953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277953 eq280085
  have eq1706665 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq276749 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq276749
    | exact resolve eq276749 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276749
  have eq1708054 : ∀ X0 X1 : G, (τ (k X1 X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1706665 X0 X1
       have i₂ := eq277406 X1
       grind)
    | exact superpose eq277406 eq1706665
    | (have j0 := eq1706665 X0 X1
       grind)
    | exact resolve eq1706665 eq277406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277406 eq1706665
  have eq1708658 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (k (σ X0) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1708054 X0 X1
       have i₂ := eq279215 X1
       grind)
    | exact superpose eq279215 eq1708054
    | (have j0 := eq1708054 X0 X1
       grind)
    | exact resolve eq1708054 eq279215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279215 eq1708054
  have eq1709028 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ (M.op X1 X1)) = X0 ∨ (k X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1708658 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq1708658
    | (have j0 := eq1708658 X0 X1
       grind)
    | exact resolve eq1708658 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708658
  have eq1717372 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1709028 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1709028
    | (have j0 := eq1709028 X1 (σ X0)
       grind)
    | exact resolve eq1709028 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709028
  have eq1718686 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (τ (M.op (σ X0) (σ X0))) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1717372 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1717372
    | (have j0 := eq1717372 X0 X1
       grind)
    | exact resolve eq1717372 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717372
  have eq1719051 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1718686 X0 X1
       have i₂ := eq280332 X0
       grind)
    | exact superpose eq280332 eq1718686
    | (have j0 := eq1718686 X0 X1
       grind)
    | exact resolve eq1718686 eq280332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718686
  have eq1719338 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1719051 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1719051
    | (have j0 := eq1719051 X0 X1
       grind)
    | exact resolve eq1719051 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719051
  have eq1721082 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq1719338 X1 X0
       grind)
    | exact superpose eq1719338 eq10
    | (have j1 := eq1719338 X1 X0
       grind)
    | exact resolve eq10 eq1719338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1721826 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1721082 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq1721082
    | (have j0 := eq1721082 X0 X1
       grind)
    | exact resolve eq1721082 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721082
  have eq1731049 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X0 X1
       have i₂ := eq1721826 X0 (σ X1)
       grind)
    | exact superpose eq1721826 eq25
    | (have j1 := eq1721826 X0 (σ X1)
       grind)
    | exact resolve eq25 eq1721826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1721826
  have eq1732895 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1731049 X0 X1
       have i₂ := eq280332 X1
       grind)
    | exact superpose eq280332 eq1731049
    | (have j0 := eq1731049 X0 X1
       grind)
    | exact resolve eq1731049 eq280332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731049
  have eq1747906 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X0 (σ X1)
       have i₂ := eq1732895 (σ X0) X1
       grind)
    | exact superpose eq1732895 eq31
    | (have j1 := eq1732895 (σ X0) X1
       grind)
    | exact resolve eq31 eq1732895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1732895
  have eq1748692 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1747906 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1747906
    | (have j0 := eq1747906 X0 X1
       grind)
    | exact resolve eq1747906 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747906
  have eq1749607 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1748692 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1748692
    | (have j0 := eq1748692 X0 X1
       grind)
    | exact resolve eq1748692 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748692
  have eq1750117 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1749607 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1749607
    | (have j0 := eq1749607 X0 X1
       grind)
    | exact resolve eq1749607 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749607
  have eq1763467 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq1750117 X0 X1
       grind)
    | exact superpose eq1750117 eq11
    | (have j1 := eq1750117 X0 X1
       grind)
    | exact resolve eq11 eq1750117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1750117
  have eq1774828 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (k x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1763467 x y
       grind)
    | exact superpose eq1763467 eq16
    | (have j1 := eq1763467 x y
       grind)
    | exact resolve eq16 eq1763467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763467
  have eq1779238 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1774828
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq1774828
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq1774828 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1779239 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1774828
       have i₂ := eq1719338 y x
       grind)
    | exact superpose eq1719338 eq1774828
    | (have j1 := eq1719338 y x
       grind)
    | (have r₁ := eq1774828
       have r₂ := eq1719338 y x
       grind)
    | exact resolve eq1774828 eq1719338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1719338 eq1774828
  have eq1779242 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1779239
  have eq1779243 : x = (k x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1779242
  have eq1779244 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1779238
  have eq1779245 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1779244
  have eq1786247 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq212 x y
       have i₂ := eq1779243
       grind)
    | exact superpose eq1779243 eq212
    | (have j0 := eq212 x y
       grind)
    | exact resolve eq212 eq1779243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq1779243
  have eq1786332 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1786247
  have eq1786352 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1786332
       have i₂ := eq280332 y
       grind)
    | exact superpose eq280332 eq1786332
    | exact resolve eq1786332 eq280332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280332 eq1786332
  have eq1786353 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1786352
  have eq1792844 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1786353
       grind)
    | exact superpose eq1786353 eq16
    | exact resolve eq16 eq1786353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786353
  have eq1792929 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1792844
       have i₂ := eq1779245
       grind)
    | exact superpose eq1779245 eq1792844
    | exact resolve eq1792844 eq1779245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779245 eq1792844
  have eq1792933 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq1792929
  have eq1792934 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq1792933
  have eq1800542 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq279945 y
       have i₂ := eq1792934
       grind)
    | exact superpose eq1792934 eq279945
    | exact resolve eq279945 eq1792934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792934
  have eq1800628 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1800542
       have r₂ := eq16
       grind)
    | exact resolve eq1800542 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800542
  have eq1801077 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1800628
       grind)
    | exact superpose eq1800628 eq10
    | exact resolve eq10 eq1800628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800628
  have eq1801826 : x = (M.op y y) := by
    first
    | (have i₁ := eq1801077
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1801077
    | exact resolve eq1801077 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1801077
  have eq1809339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq279945 y
       have i₂ := eq1801826
       grind)
    | exact superpose eq1801826 eq279945
    | exact resolve eq279945 eq1801826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279945 eq1801826
  have eq1809425 : False := by grind
  exact eq1809425

/-- `Equation645`: `x = x ◇ (y ◇ ((y ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation645 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law645 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law645.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X0))) = X0 := by
    intro X0 X1 X2
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op x (M.op (M.op x x) X0))
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : y ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq11 X1 (M.op X1 X1)
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq94 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq67 sF3
       grind)
    | exact superpose eq67 eq93
    | exact resolve eq93 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq95
       have i₂ := eq67 y
       grind)
    | exact superpose eq67 eq95
    | exact resolve eq95 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq44
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq44 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq128 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq125
    | exact resolve eq125 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq128
    | exact resolve eq128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq86
    | (have j0 := eq86 (σ x) (σ y)
       grind)
    | exact resolve eq86 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq196
    | exact resolve eq196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq200 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq197
       have r₂ := eq27
       grind)
    | exact resolve eq197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq202 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq200
    | exact resolve eq200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq204 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq27
    | exact resolve eq27 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq86 (σ X0) sF3
       grind)
    | exact superpose eq86 eq40
    | (have j1 := eq86 (σ X0) (σ y)
       grind)
    | exact resolve eq40 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq86
  have eq262 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) X0))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202 eq51
    | exact resolve eq51 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq262 eq14
    | exact resolve eq14 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq279
    | (have j0 := eq279 (σ x) (σ y)
       grind)
    | exact resolve eq279 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq318 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq52 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq289
    | exact resolve eq289 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq354 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq289 eq52
    | exact resolve eq52 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq361 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq352
  have eq363 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq361
    | exact resolve eq361 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq364 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq363
    | exact resolve eq363 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq363 eq262
    | exact resolve eq262 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq372 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq365
  have eq373 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq364
  have eq375 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq372
    | exact resolve eq372 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq419 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq375 eq51
    | exact resolve eq51 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq514 : (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq419 eq13
    | (have j0 := eq13 (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq518 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = (k (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq514
       have r₂ := eq375
       grind)
    | exact resolve eq514 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375 eq514
  have eq563 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq79
    | (have r₁ := eq79
       have r₂ := eq202
       grind)
    | exact resolve eq79 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq564 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq563
  have eq939 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq373 eq354
    | exact resolve eq354 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq954 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq939
  have eq1193 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq518
    | exact resolve eq518 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq518
  have eq1194 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1193
  have eq1195 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1194
    | exact resolve eq1194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1194
  have eq1495 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq564 eq373
    | exact resolve eq373 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq564
  have eq1535 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1495
  have eq1542 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1535 eq129
    | exact resolve eq129 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq1546 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq1542
  have eq1551 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1546
       have r₂ := eq204
       grind)
    | exact resolve eq1546 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq1546
  have eq1590 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1551 eq262
    | exact resolve eq262 eq1551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq1551
  have eq1600 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq1590
  have eq1604 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1600
    | exact resolve eq1600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600
  have eq1617 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1604 eq954
    | exact resolve eq954 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq1604
  have eq1632 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1617
  have eq1644 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1632
    | exact resolve eq1632 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1714 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1644 eq1195
    | exact resolve eq1195 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq1644
  have eq1723 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1714
  have eq1757 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1723
    | exact resolve eq1723 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq2038 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1757 eq129
    | exact resolve eq129 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1757
  have eq2041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2038
  have eq2046 : y = (M.op x y) := by
    first
    | (have r₁ := eq2041
       have r₂ := eq27
       grind)
    | exact resolve eq2041 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041
  have eq2080 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2046 eq20
    | exact resolve eq20 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2083 : y ≠ y ∨ (M.op y x) = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq2046 eq78
    | (have r₁ := eq78
       have r₂ := eq2046
       grind)
    | exact resolve eq78 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2089 : y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2046 eq318
    | exact resolve eq318 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318
  have eq2091 : (M.op y x) = (M.op y y) ∨ y = (k x y) := by grind
  clear eq2083
  have eq2092 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2089
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2089
    | exact resolve eq2089 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq2098 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2080
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2080
    | exact resolve eq2080 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2080
  have eq2099 : y = (M.op y y) := by
    first
    | exact superpose eq2046 eq2092
    | exact resolve eq2092 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092
  have eq2103 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2098 eq26
    | exact resolve eq26 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2249 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq97
       have i₂ := eq2099
       grind)
    | exact superpose eq2099 eq97
    | exact resolve eq97 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq2273 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2098 eq2249
    | exact resolve eq2249 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249
  have eq2274 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2273
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2273
    | exact resolve eq2273 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273
  have eq2275 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2098 eq2274
    | exact resolve eq2274 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2274
  have eq3224 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq2098 eq219
    | (have j0 := eq219 X0
       grind)
    | exact resolve eq219 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq3225 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2098 eq3224
    | (have j0 := eq3224 X0
       grind)
    | exact resolve eq3224 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3224
  have eq3248 : (σ (k x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3225 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3225
    | (have j0 := eq3225 x
       grind)
    | exact resolve eq3225 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3225
  have eq3263 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2103 eq3248
    | exact resolve eq3248 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3248
  have eq3278 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3263
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3263
    | exact resolve eq3263 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq3263
  have eq3289 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2098 eq3278
    | exact resolve eq3278 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3278
  have eq3298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2103 eq3289
    | exact resolve eq3289 eq2103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103 eq3289
  have eq3304 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq3298
       have r₂ := eq27
       grind)
    | exact resolve eq3298 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298
  have eq3324 : (k x (M.op x y)) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3304 eq62
    | exact resolve eq62 eq3304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq3326 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2046 eq3324
    | exact resolve eq3324 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3324
  have eq3385 : y = (M.op y x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq2091
       have i₂ := eq2099
       grind)
    | exact superpose eq2099 eq2091
    | exact resolve eq2091 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq3386 : y = (M.op y x) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3385
       have i₂ := eq3326
       grind)
    | exact superpose eq3326 eq3385
    | exact resolve eq3385 eq3326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326 eq3385
  have eq3392 : x = (M.op x (M.op y y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq52 y x
       have i₂ := eq3386
       grind)
    | exact superpose eq3386 eq52
    | exact resolve eq52 eq3386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq3386
  have eq3400 : x = (M.op x y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3392
       have i₂ := eq2099
       grind)
    | exact superpose eq2099 eq3392
    | exact resolve eq3392 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099 eq3392
  have eq3404 : x = (M.op x y) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3400
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3400
    | exact resolve eq3400 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3400
  have eq3408 : y = (τ (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq2046 eq3404
    | exact resolve eq3404 eq2046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046 eq3404
  have eq3414 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3408 eq15
    | exact resolve eq15 eq3408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3408
  have eq3427 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq3414
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3414
    | exact resolve eq3414 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3414
  have eq3429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2098 eq3427
    | exact resolve eq3427 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3427
  have eq3431 : x = y := by
    first
    | (have r₁ := eq3429
       have r₂ := eq27
       grind)
    | exact resolve eq3429 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3429
  have eq3437 : (σ (k x (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq94
       have i₂ := eq3431
       grind)
    | exact superpose eq3431 eq94
    | exact resolve eq94 eq3431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq3431
  have eq3480 : (σ (k x (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2098 eq3437
    | exact resolve eq3437 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2098 eq3437
  have eq3494 : (σ (k x (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3480
       have i₂ := eq67 sF1
       grind)
    | exact superpose eq67 eq3480
    | exact resolve eq3480 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq3480
  have eq3508 : (σ (M.op x y)) = (σ (k x (M.op x y))) := by
    first
    | exact superpose eq2275 eq3494
    | exact resolve eq3494 eq2275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275 eq3494
  have eq3520 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq45 eq3508
    | exact resolve eq3508 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3508
  have eq3529 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3304 eq3520
    | exact resolve eq3520 eq3304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3304 eq3520
  have eq3533 : False := by grind
  exact eq3533

/-- `Equation680`: `x = y ◇ (x ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation680 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law680 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law680.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq40 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq47 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq101 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq230 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq231 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq230 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq236 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq231 X0 X1
       have j1 := eq101 X0 X1
       grind)
    | (have r₁ := eq231 X0 X1
       have r₂ := eq101 X0 X1
       grind)
    | (have r₁ := eq231 X1 X1
       have r₂ := eq101 X1 X1
       grind)
    | exact resolve eq231 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq231
  have eq378 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq236 (σ X1) (σ X0)
       grind)
    | exact superpose eq236 eq15
    | exact resolve eq15 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X0 X1
       have i₂ := eq236 X1 X0
       grind)
    | exact superpose eq236 eq378
    | exact resolve eq378 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq378
  have eq388 : False := by grind
  exact eq388
