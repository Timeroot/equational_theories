import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_x_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq67 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X1 X2))) = (k (M.op (M.op X1 X0) (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq67 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq22
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq36
  have eq78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq78 y x
       grind)
    | exact superpose eq78 eq75
    | (have j1 := eq78 y x
       grind)
    | exact resolve eq75 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq110 eq78
    | (have j0 := eq78 (σ y) x
       grind)
    | exact resolve eq78 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq728
    | exact resolve eq728 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq732 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq729
       have r₂ := eq27
       grind)
    | exact resolve eq729 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq734 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq732 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq732
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq732
       grind)
    | exact resolve eq13 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq745 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq734
  have eq747 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq745 eq88
    | exact resolve eq88 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq745
  have eq751 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq747
    | exact resolve eq747 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq747
  have eq754 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78 y y
       have i₂ := eq751
       grind)
    | exact superpose eq751 eq78
    | (have j0 := eq78 y x
       grind)
    | exact resolve eq78 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq755 : y = (M.op y y) := by grind
  clear eq754
  have eq794 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq755
       grind)
    | exact superpose eq755 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq755
       grind)
    | exact resolve eq13 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq755
       grind)
    | exact superpose eq755 eq14
    | exact resolve eq14 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq755
       grind)
    | exact superpose eq755 eq14
    | exact resolve eq14 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq807 : y = (k y y) := by grind
  clear eq794
  have eq809 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq76
       have i₂ := eq807
       grind)
    | exact superpose eq807 eq76
    | exact resolve eq76 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq807
  have eq813 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq809
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq809
    | exact resolve eq809 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq830 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq813 eq78
    | (have j0 := eq78 (σ y) x
       grind)
    | exact resolve eq78 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq813
  have eq831 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq830
  have eq836 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq831 eq14
    | exact resolve eq14 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq877 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq796 (M.op y X0)
       have i₂ := eq795 X0
       grind)
    | exact superpose eq795 eq796
    | exact resolve eq796 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq795 X0
       have i₂ := eq877 X0
       grind)
    | exact superpose eq877 eq795
    | exact resolve eq795 eq877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq877
  have eq999 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq796 X0
       have i₂ := eq981 X0
       grind)
    | exact superpose eq981 eq796
    | exact resolve eq796 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq1028 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq981 X0
       have i₂ := eq999 X0
       grind)
    | exact superpose eq999 eq981
    | exact resolve eq981 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1037 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 y X0
       have i₂ := eq999 X0
       grind)
    | exact superpose eq999 eq14
    | exact resolve eq14 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1059 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1037 X0 X1
       have i₂ := eq999 X1
       grind)
    | exact superpose eq999 eq1037
    | exact resolve eq1037 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999 eq1037
  have eq1061 : y = (M.op x y) := by
    first
    | (have i₁ := eq1028 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1028
    | (have j0 := eq1028 x
       grind)
    | exact resolve eq1028 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1072 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) y)) = (k (M.op (M.op X1 X0) y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X0 y
       have i₂ := eq1028 X0
       grind)
    | exact superpose eq1028 eq68
    | exact resolve eq68 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1111 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1072 X0 x
       have i₂ := eq1028 (M.op x X0)
       grind)
    | exact superpose eq1028 eq1072
    | exact resolve eq1072 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1120 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq1111 X0
       have i₂ := eq1028 X0
       grind)
    | exact superpose eq1028 eq1111
    | exact resolve eq1111 eq1028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq1111
  have eq1124 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1061 eq20
    | exact resolve eq20 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1061
  have eq1160 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1124
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1124
    | exact resolve eq1124 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1124
  have eq1185 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1160 eq26
    | exact resolve eq26 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1260 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 y
       have i₂ := eq1120 (τ X0)
       grind)
    | exact superpose eq1120 eq38
    | exact resolve eq38 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1120
  have eq1267 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq1260 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1260
    | (have j0 := eq1260 X0
       grind)
    | exact resolve eq1260 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1260
  have eq1272 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq1160 eq1267
    | exact resolve eq1267 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq2064 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq836 X0
       have i₂ := eq1059 X0 sF3
       grind)
    | exact superpose eq1059 eq836
    | exact resolve eq836 eq1059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836 eq1059
  have eq2065 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1160 eq2064
    | exact resolve eq2064 eq1160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq2064
  have eq2068 : ∀ X0 : G, X0 ≠ X0 ∨ (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq2065 eq13
    | (have j0 := eq13 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq13 (σ (M.op x y)) X0
       have r₂ := eq2065 X0
       grind)
    | exact resolve eq13 eq2065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2065
  have eq2083 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq2068 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068
  have eq2092 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1272 eq2083
    | exact resolve eq2083 eq1272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272 eq2083
  have eq2135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2092 eq1185
    | exact resolve eq1185 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185 eq2092
  have eq2147 : False := by grind
  exact eq2147

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq60 X1 (τ X0)
       grind)
    | exact superpose eq60 eq19
    | (have j1 := eq60 X1 (τ X0)
       grind)
    | exact resolve eq19 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq83 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq99 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X4) X3) X4) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq25
    | exact resolve eq25 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq133 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq71 y x
       grind)
    | exact superpose eq71 eq16
    | (have j1 := eq71 y x
       grind)
    | exact resolve eq16 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq235 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq78 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78
    | exact resolve eq78 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq258 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq235 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq235
    | (have j0 := eq235 X0 X1
       grind)
    | exact resolve eq235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq357 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq133
       have i₂ := eq60 y x
       grind)
    | exact superpose eq60 eq133
    | (have j1 := eq60 (σ y) (σ x)
       grind)
    | exact resolve eq133 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq360 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq357
  have eq361 : y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq83
    | exact resolve eq83 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq9
    | exact resolve eq9 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 : G, (M.op (M.op (M.op x X0) y) X0) = X0 ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq361
       grind)
    | exact superpose eq361 eq9
    | exact resolve eq9 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq971 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3) = (M.op X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99 X0 X1 X2 X0 (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3)
       have i₂ := eq9 X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) X3
       grind)
    | exact superpose eq9 eq99
    | exact resolve eq99 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq992 : ∀ X0 X3 : G, (M.op X0 X3) = (M.op X0 (M.op X0 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq971 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq971
    | exact resolve eq971 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq3314 : y = (M.op (M.op x x) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq363 y
       have i₂ := eq360
       grind)
    | exact superpose eq360 eq363
    | exact resolve eq363 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq363
  have eq3362 : y = (M.op (M.op x x) y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3314
  have eq4077 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq426 x
       have i₂ := eq3362
       grind)
    | exact superpose eq3362 eq426
    | exact resolve eq426 eq3362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq3362
  have eq4129 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4077
  have eq4244 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq4129
       grind)
    | exact superpose eq4129 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4129
       grind)
    | exact resolve eq12 eq4129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4129
  have eq4291 : (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4244
  have eq4412 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq133
       have i₂ := eq4291
       grind)
    | exact superpose eq4291 eq133
    | exact resolve eq133 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq4291
  have eq4436 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4412
  have eq4437 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4436
  have eq4520 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq83 (σ y)
       have i₂ := eq4437
       grind)
    | exact superpose eq4437 eq83
    | exact resolve eq83 eq4437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4719 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4520
       grind)
    | exact superpose eq4520 eq16
    | exact resolve eq16 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4821 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq992 (σ y) (σ y)
       have i₂ := eq4437
       grind)
    | exact superpose eq4437 eq992
    | exact resolve eq992 eq4437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992 eq4437
  have eq4972 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq4821
       grind)
    | exact superpose eq4821 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4821
       grind)
    | exact resolve eq12 eq4821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4821
  have eq5023 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq4972
  have eq5033 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq5023
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5023
    | exact resolve eq5023 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5023
  have eq5038 : (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq5033
       have i₂ := eq4520
       grind)
    | exact superpose eq4520 eq5033
    | exact resolve eq5033 eq4520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4520 eq5033
  have eq5054 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq258 x y
       have i₂ := eq5038
       grind)
    | exact superpose eq5038 eq258
    | (have j0 := eq258 x y
       grind)
    | exact resolve eq258 eq5038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq5038
  have eq5104 : x = (M.op y y) := by
    first
    | (have r₁ := eq5054
       have r₂ := eq4719
       grind)
    | exact resolve eq5054 eq4719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5054
  have eq5136 : y = (M.op x y) := by
    first
    | (have i₁ := eq83 y
       have i₂ := eq5104
       grind)
    | exact superpose eq5104 eq83
    | exact resolve eq83 eq5104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq5104
  have eq5199 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq4719
       have i₂ := eq5136
       grind)
    | exact superpose eq5136 eq4719
    | exact resolve eq4719 eq5136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719 eq5136
  have eq5256 : False := by grind
  exact eq5256

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq175 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 y
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq191 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq200 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq194 eq16
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq185 eq191
    | exact resolve eq191 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq191
  have eq570 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq564
       grind)
    | exact superpose eq564 eq16
    | exact resolve eq16 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq582 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq194 eq200
    | exact resolve eq200 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq200
  have eq601 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq570 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq570
    | exact resolve eq570 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq650 : (M.op x y) = (k y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq671 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq650
       grind)
    | exact superpose eq650 eq40
    | exact resolve eq40 eq650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq650
  have eq718 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq717
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq717
    | exact resolve eq717 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq720 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq718
    | exact resolve eq718 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718
  have eq730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq720 eq661
    | exact resolve eq661 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq737 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq730
       have r₂ := eq27
       grind)
    | exact resolve eq730 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730
  have eq744 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq737 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq737 eq16
    | exact resolve eq16 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq744
    | exact resolve eq744 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq752 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq720 eq748
    | exact resolve eq748 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq748
  have eq753 : (σ x) ≠ (σ y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq752
       have r₂ := eq27
       grind)
    | exact resolve eq752 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq810 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq737 eq745
    | exact resolve eq745 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq582 eq745
    | exact resolve eq745 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq745
  have eq823 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq810
  have eq826 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq814 eq823
    | exact resolve eq823 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq823
  have eq900 : (σ x) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq826 eq737
    | exact resolve eq737 eq826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq826
  have eq908 : (σ x) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq900
  have eq913 : y = (M.op y x) := by
    first
    | (have r₁ := eq908
       have r₂ := eq753
       grind)
    | exact resolve eq908 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq908
  have eq918 : y = (M.op y y) := by
    first
    | (have i₁ := eq601 x
       have i₂ := eq913
       grind)
    | exact superpose eq913 eq601
    | exact resolve eq601 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq913
       grind)
    | exact superpose eq913 eq16
    | exact resolve eq16 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq925 : ∀ X0 : G, x = (M.op (M.op y X0) x) := by
    intro X0
    first
    | (have i₁ := eq923 X0
       have i₂ := eq601 X0
       grind)
    | exact superpose eq601 eq923
    | exact resolve eq923 eq601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601 eq923
  have eq934 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq918
       grind)
    | exact superpose eq918 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq918
       grind)
    | exact resolve eq13 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq937 : y = (k y y) := by grind
  clear eq934
  have eq945 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq937
       grind)
    | exact superpose eq937 eq41
    | exact resolve eq41 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq937
  have eq948 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq945
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq945
    | exact resolve eq945 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq955 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq948 eq671
    | (have j0 := eq671 (σ y)
       grind)
    | (have r₁ := eq671 (σ y)
       have r₂ := eq948
       grind)
    | exact resolve eq671 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq948
  have eq956 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq955
  have eq973 : x = (M.op y x) := by
    first
    | (have i₁ := eq925 y
       have i₂ := eq918
       grind)
    | exact superpose eq918 eq925
    | exact resolve eq925 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918 eq925
  have eq990 : x = y := by
    first
    | (have i₁ := eq913
       have i₂ := eq973
       grind)
    | exact superpose eq973 eq913
    | exact resolve eq913 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq994 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq973
       grind)
    | exact superpose eq973 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq995 : x ≠ x ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq973
       grind)
    | exact superpose eq973 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq973
       grind)
    | exact resolve eq13 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq998 : (M.op x y) = (k y x) := by grind
  clear eq995
  have eq1001 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq998
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq998
    | exact resolve eq998 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1002 : x = (M.op x y) ∨ x = (k x y) := by
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
  have eq1005 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq1001
       have i₂ := eq990
       grind)
    | exact superpose eq990 eq1001
    | exact resolve eq1001 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001
  have eq1006 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1002
       have i₂ := eq990
       grind)
    | exact superpose eq990 eq1002
    | exact resolve eq1002 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1009 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1006
       have i₂ := eq1005
       grind)
    | exact superpose eq1005 eq1006
    | exact resolve eq1006 eq1005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1005 eq1006
  have eq1010 : x = (M.op x y) := by grind
  clear eq1009
  have eq1014 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq990
       grind)
    | exact superpose eq990 eq24
    | exact resolve eq24 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq990
  have eq1051 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1014
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1014
    | exact resolve eq1014 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1056 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq1010
       grind)
    | exact superpose eq1010 eq22
    | exact resolve eq22 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1010
  have eq1090 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1051 eq26
    | exact resolve eq26 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1121 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1051 eq956
    | exact resolve eq956 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956 eq1051
  have eq1134 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1121 eq1090
    | exact resolve eq1090 eq1121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090 eq1121
  have eq1139 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq1134 eq27
    | exact resolve eq27 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1134
  have eq1201 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq1056 eq20
    | exact resolve eq20 eq1056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1056
  have eq1219 : False := by grind
  exact eq1219

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq43 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35
    | (have j0 := eq35 x
       grind)
    | exact resolve eq35 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq78 y x
       grind)
    | exact superpose eq78 eq75
    | (have j1 := eq78 y x
       grind)
    | exact resolve eq75 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq112 eq78
    | (have j0 := eq78 (σ y) (σ x)
       grind)
    | exact resolve eq78 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq563
    | exact resolve eq563 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq567 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq564
       have r₂ := eq27
       grind)
    | exact resolve eq564 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq571 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq567 eq14
    | exact resolve eq14 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq597 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq602 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq567 eq571
    | exact resolve eq571 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq610 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq602
  have eq859 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq571 sF3
       have i₂ := eq597 sF3
       grind)
    | exact superpose eq597 eq571
    | exact resolve eq571 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq871 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq859 eq610
    | exact resolve eq610 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610 eq859
  have eq887 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq871
  have eq899 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq887 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq887
       grind)
    | exact resolve eq13 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq908 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq899
  have eq913 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq908
    | exact resolve eq908 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908
  have eq949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq913 eq112
    | exact resolve eq112 eq913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq913
  have eq952 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq949
  have eq956 : y = (M.op y x) := by
    first
    | (have r₁ := eq952
       have r₂ := eq27
       grind)
    | exact resolve eq952 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952
  have eq960 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq956
       grind)
    | exact superpose eq956 eq14
    | exact resolve eq14 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq961 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq956
       grind)
    | exact superpose eq956 eq14
    | exact resolve eq14 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq982 : x = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq960 x
       have i₂ := eq956
       grind)
    | exact superpose eq956 eq960
    | exact resolve eq960 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1019 : y = (M.op y y) := by
    first
    | (have i₁ := eq961 y
       have i₂ := eq597 y
       grind)
    | exact superpose eq597 eq961
    | exact resolve eq961 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq961
  have eq1032 : x = (M.op y x) := by
    first
    | (have i₁ := eq982
       have i₂ := eq1019
       grind)
    | exact superpose eq1019 eq982
    | exact resolve eq982 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq982
  have eq1035 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1019
       grind)
    | exact superpose eq1019 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1019
       grind)
    | exact resolve eq13 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1045 : y = (k y y) := by grind
  clear eq1035
  have eq1046 : x = y := by
    first
    | (have i₁ := eq1032
       have i₂ := eq956
       grind)
    | exact superpose eq956 eq1032
    | exact resolve eq1032 eq956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1032
  have eq1047 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq18
    | exact resolve eq18 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1048 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq24
    | exact resolve eq24 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1064 : x = (M.op x x) := by
    first
    | (have i₁ := eq956
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq956
    | exact resolve eq956 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq1079 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1048
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1048
    | exact resolve eq1048 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1094 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1079 eq26
    | exact resolve eq26 eq1079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1079
  have eq1127 : x = (k x x) := by
    first
    | (have i₁ := eq1045
       have i₂ := eq1046
       grind)
    | exact superpose eq1046 eq1045
    | exact resolve eq1045 eq1046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045 eq1046
  have eq1129 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1127
       grind)
    | exact superpose eq1127 eq43
    | exact resolve eq43 eq1127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq1127
  have eq1133 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1129
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1129
    | exact resolve eq1129 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1129
  have eq1167 : x = (M.op x y) := by
    first
    | (have i₁ := eq1064
       have i₂ := eq1047
       grind)
    | exact superpose eq1047 eq1064
    | exact resolve eq1064 eq1047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047 eq1064
  have eq1168 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1167 eq20
    | exact resolve eq20 eq1167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1167
  have eq1199 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1168
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1168
    | exact resolve eq1168 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1168
  have eq1285 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1199 eq1133
    | exact resolve eq1133 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1289 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1285 eq78
    | (have j0 := eq78 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq78 eq1285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1285
  have eq1290 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq1289
  have eq1295 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1199 eq1094
    | exact resolve eq1094 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq1199
  have eq1322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1290 eq1295
    | exact resolve eq1295 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290 eq1295
  have eq1323 : False := by grind
  exact eq1323

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_x_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq44 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
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
  have eq90 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq44 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq44
    | exact resolve eq44 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
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
  have eq174 : y ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq175 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq176 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, y ≠ y ∨ (M.op (M.op x y) (M.op x X0)) = (k (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | exact superpose eq176 eq13
    | (have j0 := eq13 (M.op (M.op x y) (M.op x X0)) y
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) (M.op x X0)) y
       have r₂ := eq176 X0
       grind)
    | exact resolve eq13 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (k (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have j0 := eq187 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq189 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq565 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq184 eq189
    | exact resolve eq189 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq189
  have eq570 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq565
       grind)
    | exact superpose eq565 eq16
    | exact resolve eq16 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq590 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq591 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq714 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq570 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq570
    | exact resolve eq570 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq863 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq590
       grind)
    | exact superpose eq590 eq40
    | exact resolve eq40 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq864 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq863
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq863
    | exact resolve eq863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863
  have eq866 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq864
    | exact resolve eq864 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq943 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq178 X0 x x X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1036 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 X0 X1 (M.op X0 X1)
       have i₂ := eq943 (M.op X0 X1)
       grind)
    | exact superpose eq943 eq178
    | exact resolve eq178 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1040 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq943 X0
       grind)
    | exact superpose eq943 eq16
    | exact resolve eq16 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq1195 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1040 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq1040
    | exact resolve eq1040 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1199 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq179 eq1040
    | exact resolve eq1040 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq180 eq1040
    | exact resolve eq1040 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq1040
  have eq1222 : (M.op x y) ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq1199 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq1199
       grind)
    | exact resolve eq13 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1230 : x = (k x (M.op x y)) := by grind
  clear eq1222
  have eq1247 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1230 eq41
    | exact resolve eq41 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1230
  have eq1248 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1247
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1247
    | exact resolve eq1247 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1308 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq1195 X0 X1
       grind)
    | exact superpose eq1195 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq1195 X0 X1
       grind)
    | exact resolve eq13 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1340 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq2749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq866 eq591
    | exact resolve eq591 eq866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2761 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2749
       have r₂ := eq27
       grind)
    | exact resolve eq2749 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2770 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2761 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2761
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2761
       grind)
    | exact resolve eq12 eq2761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761
  have eq2786 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq2770
  have eq2794 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2786
    | exact resolve eq2786 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2786
  have eq2795 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq2794
  have eq2825 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2795 eq90
    | exact resolve eq90 eq2795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq2795
  have eq2837 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq2825
    | exact resolve eq2825 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2825
  have eq2840 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq590 eq2837
    | exact resolve eq2837 eq590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837
  have eq2841 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2840
  have eq2853 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq2841
       grind)
    | exact superpose eq2841 eq16
    | exact resolve eq16 eq2841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2864 : x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1036 y x
       have i₂ := eq2841
       grind)
    | exact superpose eq2841 eq1036
    | exact resolve eq1036 eq2841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1036
  have eq2865 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1195 y x
       have i₂ := eq2841
       grind)
    | exact superpose eq2841 eq1195
    | exact resolve eq1195 eq2841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq2841
  have eq2868 : x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2864
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2864
    | exact resolve eq2864 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864
  have eq2874 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2853 X0
       have i₂ := eq714 X0
       grind)
    | exact superpose eq714 eq2853
    | exact resolve eq2853 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq2853
  have eq3642 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2874 y
       have i₂ := eq2865
       grind)
    | exact superpose eq2865 eq2874
    | exact resolve eq2874 eq2865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2865
  have eq3672 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3642
  have eq3680 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2874 x
       have i₂ := eq3672
       grind)
    | exact superpose eq3672 eq2874
    | exact resolve eq2874 eq3672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874 eq3672
  have eq3704 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3680
  have eq3827 : (M.op (M.op x y) x) = (k (M.op (M.op x y) x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq3704
       grind)
    | exact superpose eq3704 eq188
    | exact resolve eq188 eq3704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq3704
  have eq3872 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2868 eq3827
    | exact resolve eq3827 eq2868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2868 eq3827
  have eq3883 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3872
       have r₂ := eq174
       grind)
    | exact resolve eq3872 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq3872
  have eq3893 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq3883
       grind)
    | exact superpose eq3883 eq40
    | exact resolve eq40 eq3883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq3883
  have eq3905 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3893
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3893
    | exact resolve eq3893 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq3908 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq3905
       have r₂ := eq175
       grind)
    | exact resolve eq3905 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq3905
  have eq3915 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3908 eq591
    | exact resolve eq591 eq3908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq3916 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3908 eq866
    | exact resolve eq866 eq3908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq3920 : (τ (σ x)) = (k (τ (σ x)) y) := by
    first
    | exact superpose eq3908 eq152
    | exact resolve eq152 eq3908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq3930 : x = (k x y) := by
    first
    | exact superpose eq29 eq3920
    | exact resolve eq3920 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3920
  have eq3938 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq590
       have i₂ := eq3930
       grind)
    | exact superpose eq3930 eq590
    | exact resolve eq590 eq3930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq4348 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3915 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq3915
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq3915
       grind)
    | exact resolve eq12 eq3915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3915
  have eq4367 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4348
  have eq4376 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4367
    | exact resolve eq4367 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4367
  have eq4377 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4376
  have eq4382 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3908 eq4377
    | exact resolve eq4377 eq3908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4377
  have eq4390 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4382 eq27
    | exact resolve eq27 eq4382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4382
  have eq4435 : y ≠ y ∨ y = (M.op x y) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq3916
       grind)
    | exact superpose eq3916 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq3916
       grind)
    | exact resolve eq12 eq3916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq4454 : y = (M.op x y) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4435
  have eq4466 : y = (M.op x y) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4454
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4454
    | exact resolve eq4454 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4467 : y = (M.op x y) ∨ y = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4466
  have eq4472 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4467
       have i₂ := eq3930
       grind)
    | exact superpose eq3930 eq4467
    | exact resolve eq4467 eq3930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3930 eq4467
  have eq4477 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4472 eq28
    | exact resolve eq28 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4490 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4472 eq1248
    | exact resolve eq1248 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248 eq4472
  have eq4515 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq4477
    | exact resolve eq4477 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4477
  have eq4645 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1340 y x
       have i₂ := eq3938
       grind)
    | exact superpose eq3938 eq1340
    | exact resolve eq1340 eq3938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340 eq3938
  have eq4650 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4515 eq4645
    | exact resolve eq4645 eq4515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4515 eq4645
  have eq4972 : (τ (σ x)) = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4490 eq141
    | exact resolve eq141 eq4490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq4490
  have eq4984 : x = (k x x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq4972
    | exact resolve eq4972 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4972
  have eq4987 : x = (k x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4650 eq4984
    | exact resolve eq4984 eq4650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4650 eq4984
  have eq4988 : x = (k x x) ∨ y = (M.op x y) := by grind
  clear eq4987
  have eq4999 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq636 x x
       have i₂ := eq4988
       grind)
    | exact superpose eq4988 eq636
    | (have j0 := eq636 x x
       grind)
    | (have r₁ := eq636 x x
       have r₂ := eq4988
       grind)
    | exact resolve eq636 eq4988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636 eq4988
  have eq5000 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq4999
  have eq5001 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq5000
  have eq5010 : y = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq176 x
       have i₂ := eq5001
       grind)
    | exact superpose eq5001 eq176
    | exact resolve eq176 eq5001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq5011 : x = (M.op (M.op x (M.op x y)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq5001
       grind)
    | exact superpose eq5001 eq179
    | exact resolve eq179 eq5001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq5001
  have eq5057 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1199 eq5011
    | exact resolve eq5011 eq1199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1199 eq5011
  have eq5370 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5057 eq5010
    | exact resolve eq5010 eq5057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5010 eq5057
  have eq5397 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5370
  have eq5412 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5397
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5397
    | exact resolve eq5397 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5397
  have eq5413 : y = (M.op x y) := by grind
  clear eq5412
  have eq5421 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5413
       grind)
    | exact superpose eq5413 eq24
    | exact resolve eq24 eq5413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq5468 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5421 eq20
    | exact resolve eq20 eq5421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5421
  have eq5542 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5468 eq4390
    | (have r₁ := eq4390
       have r₂ := eq5468
       grind)
    | exact resolve eq4390 eq5468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4390 eq5468
  have eq5545 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq5542
  have eq5617 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5545 eq193
    | exact resolve eq193 eq5545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq5641 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5545 eq1202
    | exact resolve eq1202 eq5545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq5684 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5641 eq5617
    | exact resolve eq5617 eq5641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5617 eq5641
  have eq5691 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq5684
    | exact resolve eq5684 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5684
  have eq5693 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq5545 eq5691
    | exact resolve eq5691 eq5545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5545 eq5691
  have eq5694 : (σ x) = (σ y) := by grind
  clear eq5693
  have eq5695 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5694 eq26
    | exact resolve eq26 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq5696 : y = (τ (σ x)) := by
    first
    | exact superpose eq5694 eq31
    | exact resolve eq31 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq5756 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5694 eq3908
    | exact resolve eq3908 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3908 eq5694
  have eq5798 : x = y := by
    first
    | exact superpose eq29 eq5696
    | exact resolve eq5696 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5696
  have eq5808 : x = (M.op x y) := by
    first
    | (have i₁ := eq5798
       have i₂ := eq5413
       grind)
    | exact superpose eq5413 eq5798
    | exact resolve eq5798 eq5413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5413 eq5798
  have eq5813 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5808
       grind)
    | exact superpose eq5808 eq22
    | exact resolve eq22 eq5808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5808
  have eq5891 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5813 eq20
    | exact resolve eq20 eq5813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5813
  have eq6020 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5695 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq5695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5695
  have eq6045 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6020
  have eq6048 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5756 eq6045
    | exact resolve eq6045 eq5756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5756 eq6045
  have eq6049 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6048
  have eq6056 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq6049 eq27
    | exact resolve eq27 eq6049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6049
  have eq6124 : False := by grind
  exact eq6124

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 X2 : G, (M.op X0 X2) = X2 ∨ (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X2
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op (M.op X1 X0) (M.op X1 X2)) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 X2)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq30 X0 X1 X2
       have j1 := eq12 X0 (M.op X1 X2)
       grind)
    | (have r₁ := eq30 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq30 X0 X1 X2
       have r₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq142 : ∀ X0 X4 : G, (M.op X0 X4) = (k X4 X0) ∨ (M.op X4 X0) = X0 := by
    intro X0 X4
    first
    | (have i₁ := eq31 X0 (M.op (M.op (M.op (M.op x X0) (M.op x x)) x) X0) x
       have i₂ := eq21 X0 x x x
       grind)
    | exact superpose eq21 eq31
    | (have j0 := eq31 X4 x X0
       grind)
    | exact resolve eq31 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq31
  have eq149 : ∀ X0 X4 : G, (M.op X0 X4) = (k X4 X0) := by
    intro X0 X4
    first
    | (have j0 := eq142 X0 X4
       have j1 := eq12 X4 X0
       grind)
    | (have r₁ := eq142 x X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq142 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq316 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq149 (σ X0) (σ X1)
       grind)
    | exact superpose eq149 eq15
    | exact resolve eq15 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq319 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq149 X0 X1
       grind)
    | exact superpose eq149 eq316
    | exact resolve eq316 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq316
  have eq322 : False := by grind
  exact eq322

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 X2 : G, (M.op X0 X2) = X2 ∨ (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) ∨ (M.op X1 X2) = (M.op X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X2
       have i₂ := eq14 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 (M.op (M.op X1 X0) (M.op X1 X2)) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 (M.op X1 X2)
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       have j1 := eq12 X0 (M.op X1 X2)
       grind)
    | (have r₁ := eq31 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq31 X0 X1 X2
       have r₂ := eq12 X0 (M.op X1 X2)
       grind)
    | exact resolve eq31 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq104 : ∀ X0 X4 : G, (M.op X0 X4) = (k X4 X0) ∨ (M.op X4 X0) = X0 := by
    intro X0 X4
    first
    | (have i₁ := eq33 X0 (M.op (M.op (M.op (M.op x X0) (M.op x x)) x) X0) x
       have i₂ := eq21 X0 x x x
       grind)
    | exact superpose eq21 eq33
    | (have j0 := eq33 X4 x X0
       grind)
    | exact resolve eq33 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq33
  have eq108 : ∀ X0 X4 : G, (M.op X0 X4) = (k X4 X0) := by
    intro X0 X4
    first
    | (have j0 := eq104 X0 X4
       have j1 := eq12 X4 X0
       grind)
    | (have r₁ := eq104 x X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq104 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq275 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq108 (σ X0) (σ X1)
       grind)
    | exact superpose eq108 eq15
    | exact resolve eq15 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq108 X0 X1
       grind)
    | exact superpose eq108 eq275
    | exact resolve eq275 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq275
  have eq281 : False := by grind
  exact eq281

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_x_pyx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq76 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq76
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq76
    | exact resolve eq76 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq83
    | exact resolve eq83 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq128 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq151 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq210 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq57 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq391 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq399 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq14
    | exact resolve eq14 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq391 X0
       grind)
    | exact superpose eq391 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq391 X0
       grind)
    | exact resolve eq13 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq401 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq613 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) X3) (σ X1)) X3) = X3 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (σ X1) (σ X0) X2 X3
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq62
    | (have j1 := eq71 X0 X1
       grind)
    | exact resolve eq62 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (σ X0) X2) (σ (k X0 X1))) X3) X2) X3) = X3 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X2 (σ X0) (σ X1) X3
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq62
    | (have j1 := eq71 X0 X1
       grind)
    | exact resolve eq62 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq621 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq71 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq623 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq621 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq958 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq399 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq399
    | exact resolve eq399 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq961 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq60 eq399
    | exact resolve eq399 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq399
  have eq982 : (M.op x y) ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq961 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq961
       grind)
    | exact resolve eq13 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq992 : x = (k x (M.op x y)) := by grind
  clear eq982
  have eq4250 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq623 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq623
    | (have j0 := eq623 (τ X0)
       grind)
    | exact resolve eq623 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq623
  have eq4258 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4250 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4250
    | (have j0 := eq4250 X0
       grind)
    | exact resolve eq4250 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4250
  have eq4264 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4258 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4258
    | (have j0 := eq4258 X0
       grind)
    | exact resolve eq4258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4258
  have eq8185 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8185
    | exact resolve eq8185 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8185
  have eq8197 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8186
       have r₂ := eq28
       grind)
    | exact resolve eq8186 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8186
  have eq8200 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8197
    | exact resolve eq8197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8197
  have eq8205 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8200 eq391
    | exact resolve eq391 eq8200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8200
  have eq8230 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8205
    | exact resolve eq8205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8205
  have eq8231 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8230
  have eq8235 : x = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq402 y
       have i₂ := eq8231
       grind)
    | exact superpose eq8231 eq402
    | exact resolve eq402 eq8231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq8231
  have eq8263 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8235
       have r₂ := eq51
       grind)
    | exact resolve eq8235 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq8235
  have eq8728 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq8263
       grind)
    | exact superpose eq8263 eq45
    | exact resolve eq45 eq8263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8263
  have eq8743 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8728
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8728
    | exact resolve eq8728 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8728
  have eq8747 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq8743
       have r₂ := eq52
       grind)
    | exact resolve eq8743 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq8743
  have eq8902 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq86 eq8747
    | exact resolve eq8747 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq9301 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq391 y
       have i₂ := eq8902
       grind)
    | exact superpose eq8902 eq391
    | exact resolve eq391 eq8902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8902
  have eq9325 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9301
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9301
    | exact resolve eq9301 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9301
  have eq9326 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq9325
  have eq9330 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9326 eq29
    | exact resolve eq29 eq9326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq9341 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9326 eq68
    | exact resolve eq68 eq9326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq9326
  have eq9441 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq151 eq9341
    | exact resolve eq9341 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq9341
  have eq9448 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq9330
    | exact resolve eq9330 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9330
  have eq9455 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq992 eq9441
    | exact resolve eq9441 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992 eq9441
  have eq9459 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9448 eq21
    | exact resolve eq21 eq9448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9589 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9459
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9459
    | exact resolve eq9459 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9459
  have eq10222 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9455 eq4264
    | (have j0 := eq4264 (M.op x y)
       grind)
    | exact resolve eq4264 eq9455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4264 eq9455
  have eq10229 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10222
       have r₂ := eq9448
       grind)
    | exact resolve eq10222 eq9448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9448 eq10222
  have eq11684 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10229 eq210
    | exact resolve eq210 eq10229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq10229
  have eq18732 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (k (σ x) (σ y))) X1) X0) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq614 x y X0 X1
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq614
    | (have j0 := eq614 x y x x
       grind)
    | exact resolve eq614 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq18864 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq8747 eq18732
    | exact resolve eq18732 eq8747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18732
  have eq18991 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18864 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18864
    | (have j0 := eq18864 X0 X1
       grind)
    | exact resolve eq18864 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18864
  have eq19115 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18991 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq18991
    | (have j0 := eq18991 X0 X1
       grind)
    | exact resolve eq18991 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18991
  have eq19224 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19115 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19115
    | (have j0 := eq19115 X0 X1
       grind)
    | exact resolve eq19115 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19115
  have eq19327 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19224 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19224
    | (have j0 := eq19224 X0 X1
       grind)
    | exact resolve eq19224 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19224
  have eq19399 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19327 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19327
    | (have j0 := eq19327 X0 X1
       grind)
    | exact resolve eq19327 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19327
  have eq19423 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq19399
    | (have j0 := eq19399 X0 X1
       grind)
    | exact resolve eq19399 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19399
  have eq19703 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq613 x y X0 X1
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq613
    | (have j0 := eq613 x y x x
       grind)
    | exact resolve eq613 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq613
  have eq20029 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19703 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19703
    | (have j0 := eq19703 X0 X1
       grind)
    | exact resolve eq19703 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19703
  have eq20209 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20029 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20029
    | (have j0 := eq20029 X0 X1
       grind)
    | exact resolve eq20029 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20029
  have eq20338 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq8747 eq20209
    | exact resolve eq20209 eq8747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8747 eq20209
  have eq20465 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20338 X1 X1
       have i₂ := eq958 sF2 X1
       grind)
    | exact superpose eq958 eq20338
    | exact resolve eq20338 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq958 eq20338
  have eq20572 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20465 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20465
    | (have j0 := eq20465 X0 X1
       grind)
    | exact resolve eq20465 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20465
  have eq20670 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20572 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20572
    | (have j0 := eq20572 X0 X1
       grind)
    | exact resolve eq20572 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20572
  have eq20744 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20670 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20670
    | (have j0 := eq20670 X0 X1
       grind)
    | exact resolve eq20670 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20670
  have eq20780 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20744 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20744
    | (have j0 := eq20744 X0 X1
       grind)
    | exact resolve eq20744 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20744
  have eq20790 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq20780
    | (have j0 := eq20780 X0 X1
       grind)
    | exact resolve eq20780 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20780
  have eq28103 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20790 eq19423
    | exact resolve eq19423 eq20790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19423 eq20790
  have eq28157 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28103
  have eq28160 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28157
    | exact resolve eq28157 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28157
  have eq28161 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28160
  have eq28168 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28161 eq391
    | exact resolve eq391 eq28161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391 eq28161
  have eq28220 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28168
    | exact resolve eq28168 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28168
  have eq28221 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28220
  have eq28225 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq28221 eq28
    | exact resolve eq28 eq28221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq28221
  have eq28273 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9589 eq28225
    | (have r₁ := eq28225
       have r₂ := eq9589
       grind)
    | exact resolve eq28225 eq9589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9589
  have eq28274 : x = (M.op x y) := by grind
  clear eq28273
  have eq28276 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28274 eq21
    | exact resolve eq21 eq28274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28368 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28274 eq11684
    | exact resolve eq11684 eq28274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11684
  have eq28377 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq28368
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28368
    | exact resolve eq28368 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28368
  have eq28440 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28276
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28276
    | exact resolve eq28276 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28276
  have eq28441 : x = y ∨ x = y := by
    first
    | exact superpose eq28274 eq28377
    | exact resolve eq28377 eq28274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28274 eq28377
  have eq28442 : x = y := by grind
  clear eq28441
  have eq28639 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq28442
       grind)
    | exact superpose eq28442 eq25
    | exact resolve eq25 eq28442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28442
  have eq28800 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28639
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28639
    | exact resolve eq28639 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq28639
  have eq28864 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28440 eq28800
    | exact resolve eq28800 eq28440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28440 eq28800
  have eq28894 : False := by grind
  exact eq28894
