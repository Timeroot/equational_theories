import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_y_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq24
  have eq66 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  have eq67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (k y x) := by
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
  have eq81 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq36
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq88 y x
       grind)
    | exact superpose eq88 eq94
    | (have j1 := eq88 y x
       grind)
    | exact resolve eq94 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq118
    | exact resolve eq118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq128 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq126
    | exact resolve eq126 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq128
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq128
    | exact resolve eq128 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq128
  have eq198 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129 eq88
    | (have j0 := eq88 (σ y) (σ x)
       grind)
    | exact resolve eq88 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq198
    | exact resolve eq198 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq202 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq199
       have r₂ := eq27
       grind)
    | exact resolve eq199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq204 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq202
    | exact resolve eq202 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq206 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq204 eq27
    | exact resolve eq27 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq895 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq204 eq81
    | (have r₁ := eq81
       have r₂ := eq204
       grind)
    | exact resolve eq81 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq896 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq895
  have eq899 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq896 eq129
    | exact resolve eq129 eq896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq903 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq899
  have eq908 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq903
       have r₂ := eq206
       grind)
    | exact resolve eq903 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq903
  have eq911 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq908 eq67
    | exact resolve eq67 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq908
  have eq948 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq911
       have r₂ := eq204
       grind)
    | exact resolve eq911 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq911
  have eq1028 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq948 eq129
    | exact resolve eq129 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq948
  have eq1031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1028
  have eq1035 : x = (M.op x y) := by
    first
    | (have r₁ := eq1031
       have r₂ := eq27
       grind)
    | exact resolve eq1031 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1037 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1035 eq20
    | exact resolve eq20 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1041 : x ≠ x ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq1035 eq80
    | (have r₁ := eq80
       have r₂ := eq1035
       grind)
    | exact resolve eq80 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1046 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq1041
  have eq1052 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1037
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1037
    | exact resolve eq1037 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1055 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1052 eq26
    | exact resolve eq26 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1542 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq94
    | exact resolve eq94 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1046
  have eq1549 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1052 eq1542
    | exact resolve eq1542 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1542
  have eq1551 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1549
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1549
    | exact resolve eq1549 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1552 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1052 eq1551
    | exact resolve eq1551 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551
  have eq1630 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1552 eq88
    | (have j0 := eq88 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq88 eq1552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552
  have eq1631 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq1630
  have eq1633 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1055 eq1631
    | exact resolve eq1631 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1631
  have eq1636 : x = (M.op x x) := by
    first
    | (have r₁ := eq1633
       have r₂ := eq27
       grind)
    | exact resolve eq1633 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq1641 : x ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq66
       have i₂ := eq1636
       grind)
    | exact superpose eq1636 eq66
    | exact resolve eq66 eq1636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1636
  have eq1674 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq1641
       have r₂ := eq1035
       grind)
    | exact resolve eq1641 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq1678 : x = (k y x) := by
    first
    | exact superpose eq1035 eq1674
    | exact resolve eq1674 eq1035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1035 eq1674
  have eq1717 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq94
       have i₂ := eq1678
       grind)
    | exact superpose eq1678 eq94
    | exact resolve eq94 eq1678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq1678
  have eq1724 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1052 eq1717
    | exact resolve eq1717 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq1726 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1724
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1724
    | exact resolve eq1724 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1724
  have eq1727 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1052 eq1726
    | exact resolve eq1726 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052 eq1726
  have eq1822 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1727 eq88
    | (have j0 := eq88 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq88 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq1727
  have eq1823 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq1822
  have eq1825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1055 eq1823
    | exact resolve eq1823 eq1055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055 eq1823
  have eq1828 : False := by grind
  exact eq1828

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq36 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq61 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq12
    | exact resolve eq12 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 x y
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq325 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq3203 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq3252 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3203 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3203
    | (have j0 := eq3203 X0 X1
       grind)
    | exact resolve eq3203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq4468 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq309
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq309
    | (have j1 := eq14 (M.op (σ x) (σ y)) (σ (M.op x x))
       grind)
    | (have r₁ := eq309
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq309
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq309 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq4469 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq4468
  have eq91651 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4469
       grind)
    | exact superpose eq4469 eq16
    | exact resolve eq16 eq4469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4469
  have eq91652 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq91651
       have r₂ := eq43 x
       grind)
    | exact resolve eq91651 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91651
  have eq141172 : y = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq91652
       grind)
    | exact superpose eq91652 eq10
    | exact resolve eq10 eq91652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91652
  have eq141334 : x = y ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq141172
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq141172
    | exact resolve eq141172 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141172
  have eq141336 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq141334
       grind)
    | exact superpose eq141334 eq16
    | exact resolve eq16 eq141334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141334
  have eq141337 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq141336
       have r₂ := eq43 x
       grind)
    | exact resolve eq141336 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141336
  have eq141775 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq141337
       grind)
    | exact superpose eq141337 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq141337
       grind)
    | exact resolve eq12 eq141337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141337
  have eq141976 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq141775
  have eq141988 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq325 x y
       have i₂ := eq141976
       grind)
    | exact superpose eq141976 eq325
    | (have j0 := eq325 x y
       grind)
    | exact resolve eq325 eq141976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq141976
  have eq141998 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq141988
  have eq141999 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq141998
  have eq142403 : y = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq141999
       grind)
    | exact superpose eq141999 eq10
    | exact resolve eq10 eq141999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141999
  have eq142565 : x = y ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq142403
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq142403
    | exact resolve eq142403 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142403
  have eq142567 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq142565
       grind)
    | exact superpose eq142565 eq16
    | exact resolve eq16 eq142565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142565
  have eq142569 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq142567
       have r₂ := eq43 x
       grind)
    | exact resolve eq142567 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq142567
  have eq143257 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq142569
       grind)
    | exact superpose eq142569 eq16
    | exact resolve eq16 eq142569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143259 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq90 x (σ y)
       have i₂ := eq142569
       grind)
    | exact superpose eq142569 eq90
    | (have j0 := eq90 x (σ y)
       grind)
    | (have r₁ := eq90 x (σ y)
       have r₂ := eq142569
       grind)
    | exact resolve eq90 eq142569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq142569
  have eq143508 : (σ (M.op x x)) = (k (σ y) (σ x)) := by grind
  clear eq143259
  have eq143530 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq143508
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq143508
    | exact resolve eq143508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143508
  have eq144259 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3252 y x
       have i₂ := eq143530
       grind)
    | exact superpose eq143530 eq3252
    | (have j0 := eq3252 (σ (M.op x y)) (σ (M.op x x))
       grind)
    | exact resolve eq3252 eq143530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252 eq143530
  have eq144426 : x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq144259
       have r₂ := eq143257
       grind)
    | exact resolve eq144259 eq143257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144259
  have eq145636 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq143257
       have i₂ := eq144426
       grind)
    | exact superpose eq144426 eq143257
    | exact resolve eq143257 eq144426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144426
  have eq145639 : (M.op x y) = (M.op x x) := by grind
  clear eq145636
  have eq145640 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq143257
       have i₂ := eq145639
       grind)
    | exact superpose eq145639 eq143257
    | exact resolve eq143257 eq145639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143257 eq145639
  have eq145848 : False := by grind
  exact eq145848

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq12 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq510 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq89 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq89 X0 X1
       grind)
    | exact superpose eq89 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq89 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq89 X0 X1
       grind)
    | exact resolve eq13 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq526 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq510 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq531 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq526 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq526 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq526 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq526 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq532 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq509 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq509 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq509 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq540 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq531 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq531
    | (have j0 := eq531 X0 X1
       grind)
    | exact resolve eq531 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq541 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq540 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq542 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq532
    | (have j0 := eq532 X0 X1
       grind)
    | exact resolve eq532 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq543 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq542 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq548 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq543 X0 X1
       have j1 := eq541 X0 X1
       grind)
    | (have r₁ := eq543 X0 X1
       have r₂ := eq541 X0 X1
       grind)
    | exact resolve eq543 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq543
  have eq549 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq548 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq548
    | exact resolve eq548 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq548 x y
       grind)
    | exact superpose eq548 eq16
    | exact resolve eq16 eq548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq667 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq549 X0 (τ X1)
       grind)
    | exact superpose eq549 eq18
    | exact resolve eq18 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq549
  have eq692 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq667 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq667
    | exact resolve eq667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq704 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq692 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq692
    | exact resolve eq692 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq731 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq560
       have i₂ := eq704 x y
       grind)
    | exact superpose eq704 eq560
    | exact resolve eq560 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq704
  have eq732 : False := by grind
  exact eq732

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyy_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq46
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq52 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq147 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq151 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       have j1 := eq55 X0 X1
       grind)
    | (have r₁ := eq147 X0 X1
       have r₂ := eq55 X0 X1
       grind)
    | (have r₁ := eq147 X0 X0
       have r₂ := eq55 X0 X0
       grind)
    | exact resolve eq147 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq147
  have eq285 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq151 (σ X0) (σ X1)
       grind)
    | exact superpose eq151 eq15
    | exact resolve eq15 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 X1
       have i₂ := eq151 X0 X1
       grind)
    | exact superpose eq151 eq285
    | exact resolve eq285 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq285
  have eq294 : False := by grind
  exact eq294

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq44 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq44 (σ X0)
       grind)
    | exact superpose eq44 eq15
    | exact resolve eq15 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq58
    | exact resolve eq58 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq58
  have eq81 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X0) X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq81
    | (have j0 := eq81 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq81 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq342 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq152
       have i₂ := eq81 x y
       grind)
    | exact superpose eq81 eq152
    | (have j1 := eq81 (σ x) (σ y)
       grind)
    | (have r₁ := eq152
       have r₂ := eq81 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq152
       have r₂ := eq81 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq152 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq152
  have eq345 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq342
  have eq346 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq345
       grind)
    | exact superpose eq345 eq16
    | exact resolve eq16 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq347 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq346
       have r₂ := eq67 x
       grind)
    | exact resolve eq346 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq383 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq347
       grind)
    | exact superpose eq347 eq10
    | exact resolve eq10 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq400 : x = y := by
    first
    | (have i₁ := eq383
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq383
    | exact resolve eq383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq444 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq400
       grind)
    | exact superpose eq400 eq16
    | exact resolve eq16 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq445 : False := by grind
  exact eq445

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_x_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op a b :=
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq39
    | exact resolve eq39 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq39
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq63 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq75 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq82 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq75 (σ X0) (σ X1)
       grind)
    | exact superpose eq75 eq15
    | (have j1 := eq75 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq75 (τ X0) X1
       grind)
    | exact superpose eq75 eq18
    | (have j1 := eq75 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq75
  have eq409 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq83 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq83
    | exact resolve eq83 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq430 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq409 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq409
    | (have j0 := eq409 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq1499 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq16
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq16 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1542 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1499
       have i₂ := eq430 x y
       grind)
    | exact superpose eq430 eq1499
    | (have j1 := eq430 (σ x) (σ y)
       grind)
    | (have r₁ := eq1499
       have r₂ := eq430 x y
       grind)
    | (have r₁ := eq1499
       have r₂ := eq430 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1499
       have r₂ := eq430 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1499 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq1499
  have eq1543 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1542
  have eq1547 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1543
       grind)
    | exact superpose eq1543 eq16
    | exact resolve eq16 eq1543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1548 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1547
       have r₂ := eq44 x
       grind)
    | exact resolve eq1547 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1547
  have eq1590 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1548
       grind)
    | exact superpose eq1548 eq16
    | exact resolve eq16 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1591 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1548
       grind)
    | exact superpose eq1548 eq10
    | exact resolve eq10 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1623 : x = y := by
    first
    | (have i₁ := eq1591
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1591
    | exact resolve eq1591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1591
  have eq1624 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1590
       have i₂ := eq44 x
       grind)
    | exact superpose eq44 eq1590
    | exact resolve eq1590 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1590
  have eq1625 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1624
       have i₂ := eq1623
       grind)
    | exact superpose eq1623 eq1624
    | exact resolve eq1624 eq1623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623 eq1624
  have eq1626 : False := by grind
  exact eq1626

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyx_pyx_pxx_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq65 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq65 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq65 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq187 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq192 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq187 X1 X0
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq187 X0 X0
       have r₂ := eq68 X0 X0
       grind)
    | exact resolve eq187 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq187
  have eq464 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq192 (σ X1) (σ X0)
       grind)
    | exact superpose eq192 eq15
    | exact resolve eq15 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq192 X1 X0
       grind)
    | exact superpose eq192 eq464
    | exact resolve eq464 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq464
  have eq471 : False := by grind
  exact eq471

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pxy_x_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq39
    | exact resolve eq39 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq39
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq44 X1
       grind)
    | exact superpose eq44 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq293 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq297 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq293 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq293 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq293 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq293 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq293
  have eq301 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq297 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq297
    | exact resolve eq297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq297 (σ X0) X1
       grind)
    | exact superpose eq297 eq15
    | (have j1 := eq297 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq315 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq301 X1 (τ X0)
       grind)
    | exact superpose eq301 eq18
    | (have j1 := eq301 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq301
  have eq663 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq315 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq315
    | exact resolve eq315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315
  have eq697 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq663
    | (have j0 := eq663 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq663 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq1418 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq306 x y
       grind)
    | exact superpose eq306 eq16
    | (have j1 := eq306 x y
       grind)
    | exact resolve eq16 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq1500 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1418
       have i₂ := eq697 x y
       grind)
    | exact superpose eq697 eq1418
    | (have j1 := eq697 (σ x) (σ y)
       grind)
    | (have r₁ := eq1418
       have r₂ := eq697 x y
       grind)
    | (have r₁ := eq1418
       have r₂ := eq697 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1418
       have r₂ := eq697 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1418 eq697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697 eq1418
  have eq1501 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1500
  have eq1505 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1501
       grind)
    | exact superpose eq1501 eq10
    | exact resolve eq10 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1548 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1505
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1505
    | exact resolve eq1505 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505
  have eq1549 : x = y := by grind
  clear eq1548
  have eq1557 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1549
       grind)
    | exact superpose eq1549 eq16
    | exact resolve eq16 eq1549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1549
  have eq1558 : False := by grind
  exact eq1558
