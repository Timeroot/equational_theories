import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3868`: `x ◇ x = (x ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation3868 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3868 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3868.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  clear eq22
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
  have eq69 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq71 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq16
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq71 x y
       grind)
    | exact superpose eq71 eq44
    | (have j1 := eq71 x y
       grind)
    | exact resolve eq44 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102
    | exact resolve eq102 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq110 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq111 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq43
    | exact resolve eq43 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq116 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq69
    | exact resolve eq69 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq118 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq81
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq81
    | exact resolve eq81 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq119 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq118
    | exact resolve eq118 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq116
    | exact resolve eq116 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq122 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq115
    | exact resolve eq115 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq115
  have eq853 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq103 eq71
    | (have j0 := eq71 (σ x) (σ y)
       grind)
    | exact resolve eq71 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq853
    | exact resolve eq853 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq857 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq854
       have r₂ := eq27
       grind)
    | exact resolve eq854 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq859 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq857
    | exact resolve eq857 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq861 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq859 eq110
    | (have r₁ := eq110
       have r₂ := eq859
       grind)
    | exact resolve eq110 eq859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq859
  have eq870 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq861
  have eq903 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq870 eq103
    | exact resolve eq103 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq870
  have eq906 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq903
  have eq908 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq906
       have r₂ := eq27
       grind)
    | exact resolve eq906 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq911 : (τ (σ y)) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq908 eq119
    | exact resolve eq119 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq908
  have eq918 : (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq911
    | exact resolve eq911 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq911
  have eq921 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq109
       have i₂ := eq918
       grind)
    | exact superpose eq918 eq109
    | (have r₁ := eq109
       have r₂ := eq918
       grind)
    | exact resolve eq109 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq922 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq122
       have i₂ := eq918
       grind)
    | exact superpose eq918 eq122
    | exact resolve eq122 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq918
  have eq930 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq921
  have eq931 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by grind
  clear eq930
  have eq933 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq922
    | exact resolve eq922 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq935 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq931
       grind)
    | exact superpose eq931 eq44
    | exact resolve eq44 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931
  have eq937 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq935
    | exact resolve eq935 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq955 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq937 eq71
    | (have j0 := eq71 (σ x) (σ y)
       grind)
    | exact resolve eq71 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq937
  have eq956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq955
    | exact resolve eq955 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq959 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq956
       have r₂ := eq27
       grind)
    | exact resolve eq956 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq961 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq959
    | exact resolve eq959 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq961 eq933
    | exact resolve eq933 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933 eq961
  have eq975 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq964
  have eq978 : y = (M.op y y) := by
    first
    | (have r₁ := eq975
       have r₂ := eq27
       grind)
    | exact resolve eq975 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq981 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq121
       have i₂ := eq978
       grind)
    | exact superpose eq978 eq121
    | exact resolve eq121 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq986 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq978
       grind)
    | exact superpose eq978 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq978
       grind)
    | exact resolve eq13 eq978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq987 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq986 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq990 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq981
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq981
    | exact resolve eq981 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq981
  have eq1050 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq990 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq990
       grind)
    | exact resolve eq13 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990
  have eq1051 : ∀ X0 : G, (k X0 (σ y)) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq1050 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1060 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq987 x
       grind)
    | exact superpose eq987 eq44
    | exact resolve eq44 eq987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq987
  have eq1069 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq1060
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1060
    | exact resolve eq1060 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1060
  have eq1070 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq1069
    | exact resolve eq1069 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1069
  have eq1246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1051 eq1070
    | exact resolve eq1070 eq1051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1051 eq1070
  have eq1261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1246
    | exact resolve eq1246 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1246
  have eq1270 : False := by grind
  exact eq1270

/-- `Equation3873`: `x ◇ x = (x ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxy_pxx_pyx_Equation3873 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3873 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3873.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
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
  have eq292 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq294 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq974 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq292 x y
       grind)
    | exact superpose eq292 eq16
    | (have j1 := eq292 x y
       grind)
    | exact resolve eq16 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq2234 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq294 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq294
    | exact resolve eq294 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2241 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = (M.op (τ X1) (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) X0
       have i₂ := eq294 X0 X1
       grind)
    | exact superpose eq294 eq13
    | (have j0 := eq13 (τ X1) X0
       have j1 := eq294 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq294 X0 X1
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq294 (M.op X0 (τ X1)) X1
       grind)
    | exact resolve eq13 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2242 : ∀ X0 X1 X2 : G, (k X2 (σ X0)) = (σ (M.op X0 (τ X2))) ∨ (M.op X1 X1) = (M.op (M.op X1 X0) X1) ∨ (τ X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (τ X2) X0
       have i₂ := eq294 X0 X2
       grind)
    | exact superpose eq294 eq9
    | (have j1 := eq294 X0 X2
       grind)
    | exact resolve eq9 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq2260 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = (M.op (τ X1) (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2241 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2241
  have eq2261 : ∀ X0 X1 : G, (τ X1) = X0 ∨ (k (τ X1) X0) = (M.op (τ X1) (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2260 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2279 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2261 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq2261
    | (have j0 := eq2261 X0 X1
       grind)
    | exact resolve eq2261 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2261
  have eq2282 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2234 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2234
    | (have j0 := eq2234 X0 X1
       grind)
    | exact resolve eq2234 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2234
  have eq8041 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq974
       have i₂ := eq2282 y x
       grind)
    | exact superpose eq2282 eq974
    | (have j1 := eq2282 (σ y) (σ x)
       grind)
    | (have r₁ := eq974
       have r₂ := eq2282 y x
       grind)
    | (have r₁ := eq974
       have r₂ := eq2282 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq974
       have r₂ := eq2282 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq974 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8042 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq8041
  have eq8044 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8042
       grind)
    | exact superpose eq8042 eq16
    | exact resolve eq16 eq8042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8042
  have eq8045 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq8044
       have r₂ := eq22 x
       grind)
    | exact resolve eq8044 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8044
  have eq8047 : x ≠ x ∨ x = y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq8045
       grind)
    | exact superpose eq8045 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8045
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq8045
       grind)
    | exact resolve eq13 eq8045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8045
  have eq8050 : x = y ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq8047
  have eq9056 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X2 X2) = (M.op (M.op X2 X1) X2) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2242 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2242
    | (have j0 := eq2242 X1 X2 X2
       grind)
    | exact resolve eq2242 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2242
  have eq9146 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X2 X2) = (M.op (M.op X2 X1) X2) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9056 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9056
    | (have j0 := eq9056 X0 X1 X2
       grind)
    | exact resolve eq9056 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9056
  have eq9204 : ∀ X0 X1 X2 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X2 X2) = (M.op (M.op X2 X0) X2) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq9146 X1 X0 X2
       grind)
    | exact superpose eq9146 eq10
    | (have j1 := eq9146 X1 X0 X2
       grind)
    | exact resolve eq10 eq9146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9146
  have eq9250 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X2 X0) X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9204 X0 X1 X2
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq9204
    | (have j0 := eq9204 X0 X1 X2
       grind)
    | exact resolve eq9204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9204
  have eq9564 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2279 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2279
    | (have j0 := eq2279 (k X0 X1) (M.op (σ X0) (σ X0))
       grind)
    | exact resolve eq2279 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2279
  have eq9680 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (k X0 X1) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9564 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9564
    | (have j0 := eq9564 X0 X1
       grind)
    | exact resolve eq9564 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9564
  have eq9687 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9680 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9680
    | (have j0 := eq9680 X0 X1
       grind)
    | exact resolve eq9680 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9680
  have eq9689 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9687 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq9687
    | (have j0 := eq9687 X0 X1
       grind)
    | exact resolve eq9687 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9687
  have eq9746 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq9689 X1 X0
       grind)
    | exact superpose eq9689 eq10
    | (have j1 := eq9689 X1 X0
       grind)
    | exact resolve eq10 eq9689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9689
  have eq9792 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9746 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq9746
    | (have j0 := eq9746 X0 X1
       grind)
    | exact resolve eq9746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9746
  have eq9830 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9792 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9792
    | (have j0 := eq9792 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq9792 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9948 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq9792 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10013 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9830 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9830
    | (have j0 := eq9830 X0 X1
       grind)
    | exact resolve eq9830 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9830
  have eq17501 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8050
       grind)
    | exact superpose eq8050 eq16
    | exact resolve eq16 eq8050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8050
  have eq17502 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y y) := by
    first
    | (have r₁ := eq17501
       have r₂ := eq22 x
       grind)
    | exact resolve eq17501 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17501
  have eq17510 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq17502
       grind)
    | exact superpose eq17502 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq17502
       grind)
    | exact resolve eq13 eq17502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17502
  have eq17525 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op y y) := by grind
  clear eq17510
  have eq17526 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (k y x) = (M.op y y) := by grind
  clear eq17525
  have eq17538 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq17526
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq17526
    | exact resolve eq17526 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17526
  have eq17546 : (k y x) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq17538
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq17538
    | exact resolve eq17538 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17538
  have eq17555 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (k y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq17546
       have i₂ := eq9792 x y
       grind)
    | exact superpose eq9792 eq17546
    | (have j1 := eq9792 x y
       grind)
    | exact resolve eq17546 eq9792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9792 eq17546
  have eq17580 : x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq9948 y x
       grind)
    | (have r₁ := eq17555
       have r₂ := eq9948 y x
       grind)
    | exact resolve eq17555 eq9948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17555
  have eq30646 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10013 y x
       grind)
    | exact superpose eq10013 eq16
    | (have j1 := eq10013 y x
       grind)
    | exact resolve eq16 eq10013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10013
  have eq39018 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (k y x) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17580
       grind)
    | exact superpose eq17580 eq16
    | exact resolve eq16 eq17580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17580
  have eq39028 : (σ x) = (σ y) ∨ (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq39018
       have r₂ := eq22 x
       grind)
    | exact resolve eq39018 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39018
  have eq39030 : y = (τ (σ x)) ∨ (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq39028
       grind)
    | exact superpose eq39028 eq10
    | exact resolve eq10 eq39028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39028
  have eq39097 : x = y ∨ (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq39030
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq39030
    | exact resolve eq39030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39030
  have eq39099 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39097
       grind)
    | exact superpose eq39097 eq16
    | exact resolve eq16 eq39097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39097
  have eq39109 : (k y x) = (M.op y y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq39099
       have r₂ := eq22 x
       grind)
    | exact resolve eq39099 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39099
  have eq39115 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2282 y x
       have i₂ := eq39109
       grind)
    | exact superpose eq39109 eq2282
    | (have j0 := eq2282 y x
       grind)
    | exact resolve eq2282 eq39109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282 eq39109
  have eq39141 : x = y ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq39115
  have eq39142 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq39141
       grind)
    | exact superpose eq39141 eq16
    | exact resolve eq16 eq39141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39141
  have eq39152 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq39142
       have r₂ := eq22 x
       grind)
    | exact resolve eq39142 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39142
  have eq39175 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x X0) = (k X0 x) ∨ x = X0 ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9250 x X0 y
       have i₂ := eq39152
       grind)
    | exact superpose eq39152 eq9250
    | (have j0 := eq9250 x X0 x
       grind)
    | exact resolve eq9250 eq39152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9250 eq39152
  have eq334447 : ∀ X0 : G, (M.op y y) = (τ (σ (M.op x y))) ∨ (M.op x X0) = (k X0 x) ∨ x = X0 ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq39175 X0
       grind)
    | exact superpose eq39175 eq10
    | (have j1 := eq39175 X0
       grind)
    | exact resolve eq10 eq39175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39175
  have eq334686 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ (M.op x X0) = (k X0 x) ∨ x = X0 ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq334447 X0
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq334447
    | (have j0 := eq334447 X0
       grind)
    | exact resolve eq334447 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334447
  have eq334687 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ (M.op x X0) = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq334686 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334686
  have eq334728 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ y = X0 ∨ (k X1 x) = (M.op x X1) ∨ x = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9948 y X1
       have i₂ := eq334687 X0
       grind)
    | exact superpose eq334687 eq9948
    | (have j0 := eq9948 (M.op x y) (k y X0)
       have j1 := eq334687 X1
       grind)
    | (have r₁ := eq9948 y x
       have r₂ := eq334687 X0
       grind)
    | exact resolve eq9948 eq334687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9948 eq334687
  have eq1146795 : ∀ X0 : G, x = y ∨ (M.op x y) = (k y x) ∨ (M.op x X0) = (k X0 x) ∨ x = X0 := by
    intro X0
    first
    | (have j0 := eq334728 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334728
  have eq1147170 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have j0 := eq1146795 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146795
  have eq1147171 : x ≠ x ∨ (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq1147170
  have eq1147172 : x = y ∨ (M.op x y) = (k y x) := by grind
  clear eq1147171
  have eq1147179 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1147172
       grind)
    | exact superpose eq1147172 eq16
    | exact resolve eq16 eq1147172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147172
  have eq1147370 : (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq1147179
       have r₂ := eq22 x
       grind)
    | exact resolve eq1147179 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147179
  have eq1147416 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq974
       have i₂ := eq1147370
       grind)
    | exact superpose eq1147370 eq974
    | exact resolve eq974 eq1147370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1147446 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq30646
       have i₂ := eq1147370
       grind)
    | exact superpose eq1147370 eq30646
    | exact resolve eq30646 eq1147370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30646 eq1147370
  have eq1147522 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by grind
  clear eq1147446
  have eq1147523 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1147416
  have eq1147533 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1147523
       grind)
    | exact superpose eq1147523 eq10
    | exact resolve eq10 eq1147523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147523
  have eq1147857 : (σ x) = (M.op (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq1147533
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1147533
    | exact resolve eq1147533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147533
  have eq1147921 : ∀ X0 : G, x = y ∨ (M.op X0 X0) = (M.op (M.op X0 (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq1147857
       grind)
    | exact superpose eq1147857 eq9
    | exact resolve eq9 eq1147857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1148371 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (M.op (M.op X0 (σ x)) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1147921 X0
       grind)
    | exact superpose eq1147921 eq16
    | (have j1 := eq1147921 X0
       grind)
    | exact resolve eq16 eq1147921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147921
  have eq1148559 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (σ x)) X0) := by
    intro X0
    first
    | (have j0 := eq1148371 X0
       grind)
    | (have r₁ := eq1148371 X0
       have r₂ := eq22 x
       grind)
    | exact resolve eq1148371 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148371
  have eq1148771 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1148559 (σ y)
       have i₂ := eq1147857
       grind)
    | exact superpose eq1147857 eq1148559
    | exact resolve eq1148559 eq1147857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147857 eq1148559
  have eq1149767 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq1148771
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq1148771
    | exact resolve eq1148771 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148771
  have eq1151131 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1149767
       grind)
    | exact superpose eq1149767 eq16
    | exact resolve eq16 eq1149767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149767
  have eq1154268 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1147522
       grind)
    | exact superpose eq1147522 eq10
    | exact resolve eq10 eq1147522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147522
  have eq1154592 : x = y ∨ (σ (M.op x y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1154268
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1154268
    | exact resolve eq1154268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154268
  have eq1154596 : x = y := by
    first
    | (have r₁ := eq1154592
       have r₂ := eq1151131
       grind)
    | exact resolve eq1154592 eq1151131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151131 eq1154592
  have eq1154599 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1154596
       grind)
    | exact superpose eq1154596 eq16
    | exact resolve eq16 eq1154596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1154596
  have eq1154786 : False := by grind
  exact eq1154786

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyx_pyx_pxy_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq2711 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq2724 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2711 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2711
  have eq2725 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2724 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724
  have eq2748 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2725 X1 X0
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq2725 X0 X1
       grind)
    | exact superpose eq2725 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq2725 X1 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq2725 X1 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq2725 X0 X0
       grind)
    | exact resolve eq12 eq2725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2749 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq2725 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq2725 X0 X1
       grind)
    | exact superpose eq2725 eq13
    | (have j1 := eq2725 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq2725 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq2725 X0 X1
       grind)
    | exact resolve eq13 eq2725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2725
  have eq2774 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2749 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2775 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2774 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2774
  have eq2776 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2748 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2748
  have eq2785 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2776 X0 X1
       have j1 := eq2775 X0 X1
       grind)
    | (have r₁ := eq2776 X0 X1
       have r₂ := eq2775 X0 X1
       grind)
    | (have r₁ := eq2776 X0 X0
       have r₂ := eq2775 X0 X0
       grind)
    | exact resolve eq2776 eq2775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775 eq2776
  have eq2836 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2785 (σ X0) (σ X1)
       grind)
    | exact superpose eq2785 eq15
    | exact resolve eq15 eq2785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2955 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2836 X0 X1
       have i₂ := eq2785 X0 X1
       grind)
    | exact superpose eq2785 eq2836
    | exact resolve eq2836 eq2785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2785 eq2836
  have eq4040 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2955 x y
       grind)
    | exact superpose eq2955 eq16
    | (have r₁ := eq16
       have r₂ := eq2955 x y
       grind)
    | exact resolve eq16 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq4060 : False := by grind
  exact eq4060

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_pyx_pyx_pxy_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq17
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
  have eq263 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X2) ≠ (M.op X2 X0) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq13 X0 X2
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X2 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq263 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq1870 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1931 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1870 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870
  have eq1932 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq2085 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq1932 (τ X0)
       grind)
    | exact superpose eq1932 eq31
    | exact resolve eq31 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2132 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2085 X0
       have i₂ := eq1932 X0
       grind)
    | exact superpose eq1932 eq2085
    | exact resolve eq2085 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932 eq2085
  have eq2309 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) X1
       have i₂ := eq2132 X0
       grind)
    | exact superpose eq2132 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2311 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq2132 X0
       grind)
    | exact superpose eq2132 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132
  have eq2314 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2309 X0 X1
       have j1 := eq2311 X0 X1
       grind)
    | (have r₁ := eq2309 X0 X1
       have r₂ := eq2311 X0 X1
       grind)
    | exact resolve eq2309 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309 eq2311
  have eq2433 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2314 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2314
    | exact resolve eq2314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314
  have eq2473 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq264 X0 X1 X1
       have i₂ := eq2433 X0 X1
       grind)
    | (have i₁ := eq264 X1 X1 X0
       have i₂ := eq2433 X0 X1
       grind)
    | exact superpose eq2433 eq264
    | (have j0 := eq264 X1 X2 X2
       have j1 := eq2433 X1 X2
       grind)
    | (have r₁ := eq264 X0 X1 X1
       have r₂ := eq2433 X0 X1
       grind)
    | (have r₁ := eq264 X1 X1 X0
       have r₂ := eq2433 X0 X1
       grind)
    | exact resolve eq264 eq2433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq2433
  have eq2488 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2473 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq2489 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X2 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2488 X2 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2488
  have eq2590 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2489 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2489
  have eq2591 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2590 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590
  have eq2630 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2591 (σ X1) (σ X0)
       grind)
    | exact superpose eq2591 eq15
    | exact resolve eq15 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2745 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2630 X0 X1
       have i₂ := eq2591 X1 X0
       grind)
    | exact superpose eq2591 eq2630
    | exact resolve eq2630 eq2591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2591 eq2630
  have eq3887 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2745 x y
       grind)
    | exact superpose eq2745 eq16
    | (have r₁ := eq16
       have r₂ := eq2745 x y
       grind)
    | exact resolve eq16 eq2745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2745
  have eq3903 : False := by grind
  exact eq3903

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq19
    | exact resolve eq19 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq38
  have eq44 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62 x y
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 x y
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq670 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq140
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq140
    | (have j1 := eq14 (M.op (σ x) (σ y)) (σ (M.op x x))
       grind)
    | (have r₁ := eq140
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq140
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq140 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq671 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq670
  have eq733 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq144 (τ X1) (τ X0)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq144
    | (have j0 := eq144 (τ X1) (τ X0)
       grind)
    | exact resolve eq144 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq748 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq733 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq733
    | (have j0 := eq733 X0 X1
       grind)
    | exact resolve eq733 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733
  have eq757 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq748 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq748
    | (have j0 := eq748 X0 X1
       grind)
    | exact resolve eq748 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq763 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq757 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq757
    | (have j0 := eq757 X0 X1
       grind)
    | exact resolve eq757 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq766 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq763 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq763
    | (have j0 := eq763 X0 X1
       grind)
    | exact resolve eq763 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq768 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq766 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq766
    | (have j0 := eq766 X0 X1
       grind)
    | exact resolve eq766 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq766
  have eq769 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq768 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq768
    | (have j0 := eq768 X0 X1
       grind)
    | exact resolve eq768 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq770 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq769 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq769
    | (have j0 := eq769 X0 X1
       grind)
    | exact resolve eq769 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq6453 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq671
       grind)
    | exact superpose eq671 eq16
    | exact resolve eq16 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671
  have eq6454 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6453
       have r₂ := eq40 x
       grind)
    | exact resolve eq6453 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6453
  have eq6456 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6454
       grind)
    | exact superpose eq6454 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6454
       grind)
    | exact resolve eq12 eq6454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6454
  have eq6464 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq6456
  have eq6468 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq144 x y
       have i₂ := eq6464
       grind)
    | exact superpose eq6464 eq144
    | (have j0 := eq144 x y
       grind)
    | exact resolve eq144 eq6464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq6464
  have eq6478 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq6468
  have eq6479 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq6478
  have eq6535 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6479
       grind)
    | exact superpose eq6479 eq16
    | exact resolve eq16 eq6479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6536 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq86 x (σ y)
       have i₂ := eq6479
       grind)
    | exact superpose eq6479 eq86
    | (have j0 := eq86 x (σ y)
       grind)
    | (have r₁ := eq86 x (σ y)
       have r₂ := eq6479
       grind)
    | exact resolve eq86 eq6479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq6479
  have eq6548 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq6536
  have eq6559 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6548
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6548
    | exact resolve eq6548 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6548
  have eq6715 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6559
       grind)
    | exact superpose eq6559 eq10
    | exact resolve eq10 eq6559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6559
  have eq6776 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6715
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6715
    | exact resolve eq6715 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6715
  have eq6778 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6776
       grind)
    | exact superpose eq6776 eq16
    | exact resolve eq16 eq6776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6776
  have eq6779 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6778
       have r₂ := eq40 x
       grind)
    | exact resolve eq6778 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6778
  have eq6951 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq6779
       grind)
    | exact superpose eq6779 eq10
    | exact resolve eq10 eq6779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6779
  have eq7015 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq6951
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq6951
    | exact resolve eq6951 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6951
  have eq7025 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq770 y x
       have i₂ := eq7015
       grind)
    | exact superpose eq7015 eq770
    | (have j0 := eq770 y x
       grind)
    | (have r₁ := eq770 y x
       have r₂ := eq7015
       grind)
    | exact resolve eq770 eq7015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq7015
  have eq7028 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq7025
  have eq7198 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7028
       grind)
    | exact superpose eq7028 eq16
    | exact resolve eq16 eq7028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7028
  have eq7201 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq7198
       have r₂ := eq40 x
       grind)
    | exact resolve eq7198 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7198
  have eq7202 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6535
       have i₂ := eq7201
       grind)
    | exact superpose eq7201 eq6535
    | exact resolve eq6535 eq7201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6535
  have eq7213 : (σ x) = (σ y) := by grind
  clear eq7202
  have eq7362 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7213
       grind)
    | exact superpose eq7213 eq16
    | exact resolve eq16 eq7213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7213
  have eq7427 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7362
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq7362
    | exact resolve eq7362 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq7362
  have eq7428 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7427
       have i₂ := eq7201
       grind)
    | exact superpose eq7201 eq7427
    | exact resolve eq7427 eq7201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7201 eq7427
  have eq7429 : False := by grind
  exact eq7429

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq64 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq65 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq75 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq65 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq76 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq75 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq91 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq76 (σ X0)
       grind)
    | exact superpose eq76 eq15
    | exact resolve eq15 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq91
    | exact resolve eq91 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq91
  have eq120 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq102
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq147 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq140 X0 X1
       have j1 := eq120 X0 X1
       grind)
    | (have r₁ := eq140 X0 X1
       have r₂ := eq120 X0 X1
       grind)
    | (have r₁ := eq140 X0 (σ (M.op X0 X0))
       have r₂ := eq120 X0 X1
       grind)
    | (have r₁ := eq140 (M.op X0 X0) (σ X0)
       have r₂ := eq120 X0 X1
       grind)
    | exact resolve eq140 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq140
  have eq169 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq147 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq147
    | exact resolve eq147 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq147 X0 (σ X1)
       grind)
    | exact superpose eq147 eq15
    | (have j1 := eq147 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq181 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq169 (τ X0) X1
       grind)
    | exact superpose eq169 eq19
    | (have j1 := eq169 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq169
  have eq267 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq181 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq181
    | exact resolve eq181 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq290 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq267 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq267
    | (have j0 := eq267 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq972 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq174 x y
       grind)
    | exact superpose eq174 eq16
    | (have j1 := eq174 x y
       grind)
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq988 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq972
       have i₂ := eq290 x y
       grind)
    | exact superpose eq290 eq972
    | (have j1 := eq290 (σ x) (σ y)
       grind)
    | (have r₁ := eq972
       have r₂ := eq290 x y
       grind)
    | (have r₁ := eq972
       have r₂ := eq290 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq972
       have r₂ := eq290 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq972 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq972
  have eq989 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq988
  have eq991 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq989
       grind)
    | exact superpose eq989 eq16
    | exact resolve eq16 eq989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq992 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq991
       have r₂ := eq102 x
       grind)
    | exact resolve eq991 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991
  have eq993 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq16
    | exact resolve eq16 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq994 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq992
       grind)
    | exact superpose eq992 eq10
    | exact resolve eq10 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1038 : x = y := by
    first
    | (have i₁ := eq994
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq994
    | exact resolve eq994 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq994
  have eq1039 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq993
       have i₂ := eq102 x
       grind)
    | exact superpose eq102 eq993
    | exact resolve eq993 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq993
  have eq1040 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1039
       have i₂ := eq1038
       grind)
    | exact superpose eq1038 eq1039
    | exact resolve eq1039 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq1039
  have eq1041 : False := by grind
  exact eq1041

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq267 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq267 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq270 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq268 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq268 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq268 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq281 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq270 (σ X0)
       grind)
    | exact superpose eq270 eq15
    | exact resolve eq15 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq300 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq281 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq281
    | exact resolve eq281 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq281
  have eq345 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq300 X0
       grind)
    | exact superpose eq300 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq347 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq345 X0 X1
       have j1 := eq346 X0 X1
       grind)
    | (have r₁ := eq345 X0 X1
       have r₂ := eq346 X0 X1
       grind)
    | exact resolve eq345 eq346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345 eq346
  have eq414 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq347 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq347 x (σ y)
       grind)
    | exact superpose eq347 eq16
    | (have j1 := eq347 x (σ y)
       grind)
    | exact resolve eq16 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq434 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq418
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq418
    | exact resolve eq418 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq445 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq414 X0 X1
       grind)
    | exact superpose eq414 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq414 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq414 X0 X1
       grind)
    | exact resolve eq13 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq456 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq445 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq463 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq456 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq456 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq456 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq488 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq463 X0 (τ X1)
       grind)
    | exact superpose eq463 eq17
    | (have j1 := eq463 X0 (τ X1)
       grind)
    | exact resolve eq17 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq494 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq463 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq488 (τ X0) X1
       grind)
    | exact superpose eq488 eq18
    | (have j1 := eq488 (τ X0) X1
       grind)
    | exact resolve eq18 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq488
  have eq817 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq810 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq810
    | (have j0 := eq810 X0 X1
       grind)
    | exact resolve eq810 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq834 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq817 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq817
    | (have j0 := eq817 X0 X1
       grind)
    | exact resolve eq817 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq837 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq834 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq834
    | (have j0 := eq834 X0 X1
       grind)
    | exact resolve eq834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq896 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq837 X0 X1
       have i₂ := eq463 X0 X1
       grind)
    | exact superpose eq463 eq837
    | (have j0 := eq837 X0 X1
       have j1 := eq463 X0 X1
       grind)
    | exact resolve eq837 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463 eq837
  have eq960 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq896 X0 X1
       have j1 := eq494 X1 X0
       grind)
    | (have r₁ := eq896 X1 X0
       have r₂ := eq494 X0 X1
       grind)
    | exact resolve eq896 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq896
  have eq1003 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq960 (σ X0) X1
       grind)
    | exact superpose eq960 eq22
    | (have j1 := eq960 (σ X0) X1
       grind)
    | exact resolve eq22 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq960
  have eq1039 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1003 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1003
    | (have j0 := eq1003 X0 X1
       grind)
    | exact resolve eq1003 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1058 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1039
    | (have j0 := eq1039 X0 X1
       grind)
    | exact resolve eq1039 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1317 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1058 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1058
    | exact resolve eq1058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1390 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1317 y x
       grind)
    | exact superpose eq1317 eq16
    | (have j1 := eq1317 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1317 y x
       grind)
    | exact resolve eq16 eq1317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1317
  have eq1409 : x = (k y x) := by grind
  clear eq1390
  have eq1595 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq434
       have i₂ := eq414 x y
       grind)
    | exact superpose eq414 eq434
    | (have j1 := eq414 x y
       grind)
    | exact resolve eq434 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1596 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by grind
  clear eq1595
  have eq1598 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1596
       have i₂ := eq1409
       grind)
    | exact superpose eq1409 eq1596
    | exact resolve eq1596 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1600 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1598
       have i₂ := eq1409
       grind)
    | exact superpose eq1409 eq1598
    | exact resolve eq1598 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1601 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq434
       have i₂ := eq1600
       grind)
    | exact superpose eq1600 eq434
    | exact resolve eq434 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434 eq1600
  have eq1610 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1601
  have eq1611 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1610
       have i₂ := eq1409
       grind)
    | exact superpose eq1409 eq1610
    | exact resolve eq1610 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq1612 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1611
  have eq1614 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1612
       grind)
    | exact superpose eq1612 eq16
    | exact resolve eq16 eq1612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1612
  have eq1633 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq1614
       have i₂ := eq414 x y
       grind)
    | exact superpose eq414 eq1614
    | (have j1 := eq414 x y
       grind)
    | exact resolve eq1614 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq1634 : (M.op x y) = (k y x) := by grind
  clear eq1633
  have eq1637 : x = (M.op x y) := by
    first
    | (have i₁ := eq1634
       have i₂ := eq1409
       grind)
    | exact superpose eq1409 eq1634
    | exact resolve eq1634 eq1409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409 eq1634
  have eq1638 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1614
       have i₂ := eq1637
       grind)
    | exact superpose eq1637 eq1614
    | exact resolve eq1614 eq1637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1614 eq1637
  have eq1649 : False := by grind
  exact eq1649

/-- `Equation3912`: `x ◇ x = (y ◇ (z ◇ w)) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyy_pyx_pxy_Equation3912 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3912 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3912.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X3)) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : (M.op x y) = (M.op x y) := by grind
  have eq20 : (M.op x y) = (M.op x y) := by grind
  clear eq19
  have eq21 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq22 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq21
  have eq23 : (σ x) = (σ x) := by grind
  have eq24 : (σ x) = (σ x) := by grind
  clear eq23
  have eq25 : (σ y) = (σ y) := by grind
  have eq26 : (σ y) = (σ y) := by grind
  clear eq25
  have eq27 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq28 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq27
  have eq29 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq30 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq10
    | (have j0 := eq10 y X0
       grind)
    | exact resolve eq10 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq22 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X5 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X0)) X5) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq14 X1 X2 (M.op x (M.op x X5)) X5
       have i₂ := eq14 X0 x x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op x y)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq28 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 X5 : G, (M.op X3 X3) = (M.op (M.op (M.op X0 (M.op X1 X2)) X2) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op x X5) x X5
       have i₂ := eq14 (M.op x X5) X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X5 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X5) := by
    intro X0 X1 X5
    first
    | (have i₁ := eq14 X1 (M.op x (M.op x (M.op x X5))) x X5
       have i₂ := eq14 X0 x x (M.op x X5)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x x x
       have i₂ := eq14 X1 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X1 X1)) := by
    intro X0 X1
    grind
  have eq86 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X2) = (k X3 (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    grind
  have eq87 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (k X0 (M.op X0 X0)) X0) := by
    intro X0 X1
    grind
  have eq97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq102
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq102
    | exact resolve eq102 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22 eq110
    | exact resolve eq110 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq116 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq127 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq117
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq117 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq16
    | exact resolve eq16 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq127
  have eq134 : ∀ X1 : G, (k (M.op X1 X1) X1) = (M.op X1 (M.op X1 X1)) ∨ (k X1 (M.op X1 X1)) = X1 := by
    intro X1
    grind
  have eq148 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X0 (M.op X1 X2)) X2) X3) = (M.op X3 (M.op (M.op X0 (M.op X1 X2)) X2)) ∨ (k X3 (M.op (M.op X0 (M.op X1 X2)) X2)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq134 X0
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq134
    | exact resolve eq134 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq161 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq39
    | (have j0 := eq39 (M.op x y)
       grind)
    | exact resolve eq39 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq195 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq161 eq16
    | exact resolve eq16 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq290 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (k X0 (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    grind
  have eq388 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq84 X1 X2
       have i₂ := eq59 X2 X0
       grind)
    | (have i₁ := eq84 X1 X2
       have i₂ := eq59 X0 X2
       grind)
    | exact superpose eq59 eq84
    | exact resolve eq84 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq40 X1 X0
       grind)
    | exact superpose eq40 eq16
    | exact resolve eq16 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq576 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (M.op X2 (M.op X3 X4)) X4) X5) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq57 X2 X3 X4 x X5
       have i₂ := eq56 x X0
       grind)
    | exact superpose eq56 eq57
    | exact resolve eq57 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq710 : ∀ X0 X1 X2 X4 X5 : G, (k X5 (M.op X5 X5)) = (M.op (M.op (M.op X0 (M.op X1 X1)) X2) X4) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq86 (M.op x X4) x X4 X5
       have i₂ := eq54 X1 (M.op x X4) X0 X2
       grind)
    | (have i₁ := eq86 (M.op X2 (M.op X0 X0)) X1 X2 x
       have i₂ := eq54 X0 X1 X2 (M.op X1 X2)
       grind)
    | exact superpose eq54 eq86
    | exact resolve eq86 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq721 : ∀ X0 X4 X5 : G, (k X5 (M.op X5 X5)) = (M.op (k X0 (M.op X0 X0)) X4) := by
    intro X0 X4 X5
    first
    | (have i₁ := eq86 (M.op x (M.op x (M.op x X4))) x X4 X5
       have i₂ := eq86 x x (M.op x X4) X0
       grind)
    | exact superpose eq86 eq86
    | exact resolve eq86 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq754 : ∀ X0 X1 X5 X6 : G, (M.op X1 X1) = (M.op (M.op (k X0 (M.op X0 X0)) X5) X6) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq57 (M.op x (M.op x (M.op x X5))) x X5 X1 X6
       have i₂ := eq86 x x (M.op x X5) X0
       grind)
    | exact superpose eq86 eq57
    | exact resolve eq57 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq86
  have eq849 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36 X1 (M.op X2 X2)
       have i₂ := eq388 X2 X0 (τ X1)
       grind)
    | exact superpose eq388 eq36
    | exact resolve eq36 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1278 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq429 X1 (M.op X2 X2)
       have i₂ := eq388 X2 X0 (σ X1)
       grind)
    | exact superpose eq388 eq429
    | exact resolve eq429 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq1817 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 X0
       have i₂ := eq59 (σ X0) X1
       grind)
    | (have i₁ := eq97 X0 X0
       have i₂ := eq59 X0 (σ X0)
       grind)
    | exact superpose eq59 eq97
    | exact resolve eq97 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1833 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 X1 (σ X0)
       have i₂ := eq97 X0 X0
       grind)
    | exact superpose eq97 eq59
    | (have j1 := eq97 X0 X0
       grind)
    | exact resolve eq59 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1854 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq97 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq1855 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1854 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1854
  have eq1869 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1833 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1885 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1817 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq2294 : ∀ X0 X2 X3 : G, (k (M.op (M.op (k X0 (M.op X0 X0)) X0) X2) X3) = (M.op X3 (M.op (M.op (k X0 (M.op X0 X0)) X0) X2)) ∨ (k X3 (M.op (M.op (k X0 (M.op X0 X0)) X0) X2)) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq148 (M.op x X2) x X2 X3
       have i₂ := eq87 X0 (M.op x X2)
       grind)
    | exact superpose eq87 eq148
    | exact resolve eq148 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq148
  have eq3916 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (k X2 (M.op X0 X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq290 X2 X1 X3
       have i₂ := eq59 X2 X0
       grind)
    | (have i₁ := eq290 X2 X1 X3
       have i₂ := eq59 X0 X2
       grind)
    | exact superpose eq59 eq290
    | exact resolve eq290 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq17143 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op X1 X1)) = (M.op (k X2 (k X0 (M.op X0 X0))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq721 X2 X3 X1
       have i₂ := eq84 X2 X0
       grind)
    | exact superpose eq84 eq721
    | exact resolve eq721 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq18549 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X1) = (M.op (M.op (k X2 (k X0 (M.op X0 X0))) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq754 X2 X1 X3 X4
       have i₂ := eq84 X2 X0
       grind)
    | exact superpose eq84 eq754
    | exact resolve eq754 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq754
  have eq20942 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq849 X0 x x
       have i₂ := eq849 X1 x x
       grind)
    | exact superpose eq849 eq849
    | exact resolve eq849 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21353 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1278 X0 x x
       have i₂ := eq1278 X1 x x
       grind)
    | exact superpose eq1278 eq1278
    | exact resolve eq1278 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23351 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq36 X1 (τ X1)
       have i₂ := eq1885 X0 (τ X1)
       grind)
    | exact superpose eq1885 eq36
    | (have j1 := eq1885 X0 (τ X1)
       grind)
    | exact resolve eq36 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23352 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq45
       have i₂ := eq1885 X0 x
       grind)
    | exact superpose eq1885 eq45
    | (have j1 := eq1885 X0 x
       grind)
    | exact resolve eq45 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23353 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq117
       have i₂ := eq1885 X0 y
       grind)
    | exact superpose eq1885 eq117
    | (have j1 := eq1885 X0 y
       grind)
    | exact resolve eq117 eq1885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885
  have eq23373 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq23353 X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq23353
    | (have j0 := eq23353 X0
       grind)
    | exact resolve eq23353 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23353
  have eq23374 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq23352 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23352
    | (have j0 := eq23352 X0
       grind)
    | exact resolve eq23352 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23352
  have eq23375 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23351 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq23351
    | (have j0 := eq23351 X0 X1
       grind)
    | exact resolve eq23351 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23351
  have eq23418 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23375 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq23375
    | (have j0 := eq23375 X0 X1
       grind)
    | exact resolve eq23375 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23375
  have eq47309 : ∀ X0 X1 X6 X7 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (k X0 (M.op X0 X0)) X6) X7) := by
    intro X0 X1 X6 X7
    first
    | (have i₁ := eq576 X1 (M.op (M.op x (M.op x x)) x) x X6 X7
       have i₂ := eq710 x x x (M.op x X6) X0
       grind)
    | exact superpose eq710 eq576
    | exact resolve eq576 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq710
  have eq74578 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1855 (τ X0)
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq1855
    | (have j0 := eq1855 (τ X0)
       grind)
    | exact resolve eq1855 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1855
  have eq74586 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq74578 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq74578
    | (have j0 := eq74578 X0
       grind)
    | exact resolve eq74578 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74578
  have eq74610 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq74586 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq74586
    | (have j0 := eq74586 X0
       grind)
    | exact resolve eq74586 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74586
  have eq74666 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = (σ (k (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1869 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1869
    | (have j0 := eq1869 (τ X0) X1
       grind)
    | exact resolve eq1869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74693 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1869 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1869
    | (have j0 := eq1869 x X0
       grind)
    | exact resolve eq1869 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74694 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq1869 y X0
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1869
    | (have j0 := eq1869 y X0
       grind)
    | exact resolve eq1869 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74695 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq22 eq1869
    | (have j0 := eq1869 (M.op x y) X0
       grind)
    | exact resolve eq1869 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq75050 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq161 eq74695
    | exact resolve eq74695 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161 eq74695
  have eq75051 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq74694 X0
       have i₂ := eq117
       grind)
    | exact superpose eq117 eq74694
    | exact resolve eq74694 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq74694
  have eq75052 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq74693 X0
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq74693
    | exact resolve eq74693 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq74693
  have eq75054 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (σ (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74666 X0 X1
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq74666
    | (have j0 := eq74666 X0 X1
       grind)
    | exact resolve eq74666 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq74666
  have eq75073 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75054 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq75054
    | (have j0 := eq75054 X0 X1
       grind)
    | exact resolve eq75054 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75054
  have eq140648 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq23418 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23418
  have eq140765 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op X2 X2) = (σ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140648 X2 (σ (M.op X1 X1))
       have i₂ := eq849 X0 (σ (M.op X1 X1)) X1
       grind)
    | exact superpose eq849 eq140648
    | (have j0 := eq140648 X2 (σ (M.op X1 X1))
       grind)
    | (have r₁ := eq140648 X0 (σ (M.op X0 X0))
       have r₂ := eq849 X0 (σ (M.op X0 X0)) X0
       grind)
    | exact resolve eq140648 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq140767 : ∀ X0 X1 X2 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X1 X1)) ∨ (M.op X2 X2) = (τ (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq140648 X2 (τ (M.op X1 X1))
       have i₂ := eq1278 X0 (τ (M.op X1 X1)) X1
       grind)
    | exact superpose eq1278 eq140648
    | (have j0 := eq140648 X2 (τ (M.op X1 X1))
       grind)
    | (have r₁ := eq140648 X0 (τ (M.op X0 X0))
       have r₂ := eq1278 X0 (τ (M.op X0 X0)) X0
       grind)
    | exact resolve eq140648 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278 eq140648
  have eq140774 : ∀ X1 X2 : G, (M.op X2 X2) = (τ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq140767 x X1 X2
       grind)
    | (have r₁ := eq140767 x X1 X2
       have r₂ := eq21353 x X1
       grind)
    | (have r₁ := eq140767 X1 x X2
       have r₂ := eq21353 x X1
       grind)
    | exact resolve eq140767 eq21353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21353 eq140767
  have eq140775 : ∀ X1 X2 : G, (M.op X2 X2) = (σ (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq140765 x X1 X2
       grind)
    | (have r₁ := eq140765 x X1 X2
       have r₂ := eq20942 x X1
       grind)
    | (have r₁ := eq140765 X1 x X2
       have r₂ := eq20942 x X1
       grind)
    | exact resolve eq140765 eq20942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20942 eq140765
  have eq141832 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (τ (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq140774 X3 x
       have i₂ := eq58 X0 x X1
       grind)
    | (have i₁ := eq140774 X1 (M.op X0 X0)
       have i₂ := eq58 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq58 eq140774
    | exact resolve eq140774 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142011 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq140774 x X1
       have i₂ := eq55 x X0
       grind)
    | exact superpose eq55 eq140774
    | exact resolve eq140774 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142078 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (τ (M.op (k X0 (M.op X1 X1)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq140774 x X3
       have i₂ := eq3916 X1 x X0 X2
       grind)
    | (have i₁ := eq140774 (k X2 (M.op X0 X0)) X2
       have i₂ := eq3916 X0 X1 X2 (k X2 (M.op X0 X0))
       grind)
    | exact superpose eq3916 eq140774
    | exact resolve eq140774 eq3916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142080 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ y) (σ y))) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq140774 X1 X0
       have i₂ := eq23373 X1
       grind)
    | exact superpose eq23373 eq140774
    | (have j1 := eq23373 X1
       grind)
    | exact resolve eq140774 eq23373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23373
  have eq142081 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (k (σ x) (σ x))) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq140774 X1 X0
       have i₂ := eq23374 X1
       grind)
    | exact superpose eq23374 eq140774
    | (have j1 := eq23374 X1
       grind)
    | exact resolve eq140774 eq23374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23374
  have eq142210 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (M.op (τ (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq58 x X1 X3
       have i₂ := eq140774 X0 x
       grind)
    | exact superpose eq140774 eq58
    | exact resolve eq58 eq140774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq142827 : ∀ X0 X1 : G, (M.op X0 X0) = (k x x) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | exact superpose eq51 eq142081
    | (have j0 := eq142081 X0 X1
       grind)
    | exact resolve eq142081 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142081
  have eq142828 : ∀ X0 X1 : G, (M.op X0 X0) = (k y y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq132 eq142080
    | (have j0 := eq142080 X0 X1
       grind)
    | exact resolve eq142080 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142080
  have eq142906 : ∀ X0 X2 : G, (σ (M.op X2 X2)) = (τ (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq140775 X2 x
       have i₂ := eq140774 X0 x
       grind)
    | exact superpose eq140774 eq140775
    | exact resolve eq140775 eq140774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143017 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op (M.op X0 (M.op x y)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq140775 x X1
       have i₂ := eq55 x X0
       grind)
    | exact superpose eq55 eq140775
    | exact resolve eq140775 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq143084 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (σ (M.op (k X0 (M.op X1 X1)) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq140775 x X3
       have i₂ := eq3916 X1 x X0 X2
       grind)
    | (have i₁ := eq140775 (k X2 (M.op X0 X0)) X2
       have i₂ := eq3916 X0 X1 X2 (k X2 (M.op X0 X0))
       grind)
    | exact superpose eq3916 eq140775
    | exact resolve eq140775 eq3916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3916
  have eq155514 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op (τ (M.op X0 X0)) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq142011 (M.op X0 X0) X1
       have i₂ := eq141832 X0 sF0 x
       grind)
    | exact superpose eq141832 eq142011
    | exact resolve eq142011 eq141832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141832 eq142011
  have eq174552 : ∀ X0 X1 X3 : G, (τ (M.op X3 X3)) = (σ (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq142906 X3 x
       have i₂ := eq142210 X0 x X1
       grind)
    | (have i₁ := eq142906 X0 (τ (M.op X0 X0))
       have i₂ := eq142210 X0 X1 (τ (M.op X0 X0))
       grind)
    | exact superpose eq142210 eq142906
    | exact resolve eq142906 eq142210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142210 eq142906
  have eq623310 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq75050 eq74610
    | (have j0 := eq74610 (σ (M.op x y))
       grind)
    | exact resolve eq74610 eq75050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623328 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq623310 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623310
  have eq625406 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq75051 eq74610
    | (have j0 := eq74610 (σ y)
       grind)
    | exact resolve eq74610 eq75051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75051
  have eq625424 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq625406 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625406
  have eq625485 : ∀ X0 X1 : G, (σ y) ≠ (k X0 (M.op X1 X1)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq625424 x
       have i₂ := eq388 X1 x X0
       grind)
    | exact superpose eq388 eq625424
    | exact resolve eq625424 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq625580 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq625424 x
       have i₂ := eq140775 X0 x
       grind)
    | exact superpose eq140775 eq625424
    | exact resolve eq625424 eq140775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627506 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq75052 eq74610
    | (have j0 := eq74610 (σ x)
       grind)
    | exact resolve eq74610 eq75052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627524 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq627506 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627506
  have eq627681 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq627524 x
       have i₂ := eq140775 X0 x
       grind)
    | exact superpose eq140775 eq627524
    | exact resolve eq627524 eq140775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629736 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq74610 X1
       have i₂ := eq75073 X1 X0
       grind)
    | exact superpose eq75073 eq74610
    | (have j0 := eq74610 X1
       have j1 := eq75073 X1 X1
       grind)
    | (have r₁ := eq74610 (M.op X1 X1)
       have r₂ := eq75073 (M.op X1 X1) X1
       grind)
    | exact resolve eq74610 eq75073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74610 eq75073
  have eq629984 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq629736 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629736
  have eq632236 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq133
       have i₂ := eq140775 y X0
       grind)
    | exact superpose eq140775 eq133
    | exact resolve eq133 eq140775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq140775
  have eq1099402 : ∀ X1 : G, (k x x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X1 X1) = (σ x) := by
    intro X1
    first
    | (have i₁ := eq75052 x
       have i₂ := eq142827 x X1
       grind)
    | exact superpose eq142827 eq75052
    | (have j1 := eq142827 x (σ x)
       grind)
    | exact resolve eq75052 eq142827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142827
  have eq1100843 : (k x x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq1099402 (σ x)
       grind)
    | (have r₁ := eq1099402 x
       have r₂ := eq627524 (σ x)
       grind)
    | (have r₁ := eq1099402 x
       have r₂ := eq627524 x
       grind)
    | exact resolve eq1099402 eq627524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099402
  have eq1102100 : ∀ X0 X2 : G, (σ y) ≠ (k X0 (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq625485 X0 x
       have i₂ := eq142828 x X2
       grind)
    | exact superpose eq142828 eq625485
    | (have j1 := eq142828 X0 (σ y)
       grind)
    | exact resolve eq625485 eq142828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142828 eq625485
  have eq1103202 : ∀ X0 : G, (σ y) ≠ (k X0 (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1102100 X0 (σ y)
       grind)
    | (have r₁ := eq1102100 X0 x
       have r₂ := eq625424 (σ y)
       grind)
    | (have r₁ := eq1102100 X0 X0
       have r₂ := eq625424 X0
       grind)
    | exact resolve eq1102100 eq625424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102100
  have eq1878811 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq1878819 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq28 eq1878811
    | exact resolve eq1878811 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878811
  have eq1878830 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1878819
       have r₂ := eq29
       grind)
    | exact resolve eq1878819 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878819
  have eq1878832 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1878830
       have i₂ := eq59 sF2 x
       grind)
    | (have i₁ := eq1878830
       have i₂ := eq59 X0 sF2
       grind)
    | exact superpose eq59 eq1878830
    | exact resolve eq1878830 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878830
  have eq1879765 : ∀ X0 X1 : G, y = (M.op x x) ∨ (M.op X1 X1) = (σ y) ∨ x = (M.op y y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq1878832 X0
       have i₂ := eq59 sF3 X1
       grind)
    | (have i₁ := eq1878832 X0
       have i₂ := eq59 X0 sF3
       grind)
    | exact superpose eq59 eq1878832
    | (have j0 := eq1878832 X1
       grind)
    | exact resolve eq1878832 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878832
  have eq1889379 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ x = (M.op y y) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq625580 x
       have i₂ := eq1879765 X1 X0
       grind)
    | exact superpose eq1879765 eq625580
    | (have j1 := eq1879765 X1 (σ y)
       grind)
    | exact resolve eq625580 eq1879765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625580 eq1879765
  have eq1889598 : ∀ X1 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op X1 X1) = (σ x) := by
    intro X1
    first
    | (have j0 := eq1889379 (σ y) X1
       grind)
    | (have r₁ := eq1889379 x X1
       have r₂ := eq625424 (σ y)
       grind)
    | (have r₁ := eq1889379 x X1
       have r₂ := eq625424 x
       grind)
    | exact resolve eq1889379 eq625424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625424 eq1889379
  have eq1889689 : ∀ X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op X1 X1) = (σ x) := by
    intro X1
    first
    | (have j0 := eq1889598 X1
       grind)
    | (have r₁ := eq1889598 X1
       have r₂ := eq26
       grind)
    | exact resolve eq1889598 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889598
  have eq1889694 : ∀ X0 X1 : G, x = (M.op y y) ∨ (M.op X0 X0) = (σ y) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq1889689 X1
       have i₂ := eq59 sF3 X1
       grind)
    | (have i₁ := eq1889689 X1
       have i₂ := eq59 X0 sF3
       grind)
    | exact superpose eq59 eq1889689
    | (have j0 := eq1889689 X1
       grind)
    | exact resolve eq1889689 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889689
  have eq1895493 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ y) ∨ (M.op X1 X1) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq627681 y
       have i₂ := eq1889694 X0 X1
       grind)
    | exact superpose eq1889694 eq627681
    | (have j1 := eq1889694 X0 (σ x)
       grind)
    | exact resolve eq627681 eq1889694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627681 eq1889694
  have eq1895697 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1895493 X0 (σ x)
       grind)
    | (have r₁ := eq1895493 X0 x
       have r₂ := eq627524 (σ x)
       grind)
    | (have r₁ := eq1895493 X0 X0
       have r₂ := eq627524 X0
       grind)
    | exact resolve eq1895493 eq627524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895493
  have eq1895793 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq1895697 X0
       grind)
    | (have r₁ := eq1895697 X0
       have r₂ := eq24
       grind)
    | exact resolve eq1895697 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895697
  have eq1895799 : ∀ X0 X1 : G, (M.op X1 X1) = (σ y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0 X1
    first
    | (have i₁ := eq1895793 X0
       have i₂ := eq59 sF2 X1
       grind)
    | (have i₁ := eq1895793 X0
       have i₂ := eq59 X0 sF2
       grind)
    | exact superpose eq59 eq1895793
    | (have j0 := eq1895793 X1
       grind)
    | exact resolve eq1895793 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896099 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ x)) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq140774 X0 x
       have i₂ := eq1895793 X0
       grind)
    | exact superpose eq1895793 eq140774
    | (have j1 := eq1895793 X1
       grind)
    | exact resolve eq140774 eq1895793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896306 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op (τ (σ x)) y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq155514 X0 X1
       have i₂ := eq1895793 X0
       grind)
    | exact superpose eq1895793 eq155514
    | (have j1 := eq1895793 X1
       grind)
    | exact resolve eq155514 eq1895793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155514 eq1895793
  have eq1896656 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op x y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq30 eq1896306
    | (have j0 := eq1896306 X0 X1
       grind)
    | exact resolve eq1896306 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896306
  have eq1896720 : ∀ X0 X1 : G, (M.op X1 X1) = (σ y) ∨ (M.op X0 X0) = x := by
    intro X0 X1
    first
    | exact superpose eq30 eq1896099
    | (have j0 := eq1896099 X0 X1
       grind)
    | exact resolve eq1896099 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896099
  have eq1896733 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op x y)) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1896656 X0 X1
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1896656
    | (have j0 := eq1896656 X0 X1
       grind)
    | exact resolve eq1896656 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896656
  have eq1897842 : ∀ X1 : G, (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X1 X1) = (σ x) := by
    intro X1
    first
    | (have i₁ := eq75052 x
       have i₂ := eq1895799 X1 x
       grind)
    | (have i₁ := eq75052 x
       have i₂ := eq1895799 x X1
       grind)
    | exact superpose eq1895799 eq75052
    | (have j1 := eq1895799 (σ x) X1
       grind)
    | exact resolve eq75052 eq1895799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75052
  have eq1899813 : ∀ X0 X3 : G, (M.op X0 X0) = (τ (σ y)) ∨ (σ x) = (M.op X3 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq142078 x x (k x (M.op x x)) X0
       have i₂ := eq1895799 X3 (k x (M.op x x))
       grind)
    | (have i₁ := eq142078 X0 x (k X0 (M.op x x)) X3
       have i₂ := eq1895799 (k X0 (M.op x x)) x
       grind)
    | exact superpose eq1895799 eq142078
    | (have j1 := eq1895799 X3 x
       grind)
    | exact resolve eq142078 eq1895799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895799
  have eq1899867 : ∀ X0 X3 : G, (σ x) = (M.op X3 X3) ∨ (M.op X0 X0) = y := by
    intro X0 X3
    first
    | exact superpose eq31 eq1899813
    | (have j0 := eq1899813 X0 X3
       grind)
    | exact resolve eq1899813 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899813
  have eq1900075 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq1897842 (σ x)
       grind)
    | (have r₁ := eq1897842 x
       have r₂ := eq627524 (σ x)
       grind)
    | (have r₁ := eq1897842 x
       have r₂ := eq627524 x
       grind)
    | exact resolve eq1897842 eq627524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897842
  have eq1906388 : ∀ X0 X3 : G, (M.op X0 X0) = (τ (σ y)) ∨ x = (M.op X3 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq142078 x x (k x (M.op x x)) X0
       have i₂ := eq1896720 X3 (k x (M.op x x))
       grind)
    | (have i₁ := eq142078 X0 x (k X0 (M.op x x)) X3
       have i₂ := eq1896720 (k X0 (M.op x x)) x
       grind)
    | exact superpose eq1896720 eq142078
    | (have j1 := eq1896720 X3 x
       grind)
    | exact resolve eq142078 eq1896720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142078 eq1896720
  have eq1906442 : ∀ X0 X3 : G, x = (M.op X3 X3) ∨ (M.op X0 X0) = y := by
    intro X0 X3
    first
    | exact superpose eq31 eq1906388
    | (have j0 := eq1906388 X0 X3
       grind)
    | exact resolve eq1906388 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906388
  have eq1910308 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 sF4
       have i₂ := eq1899867 X0 sF4
       grind)
    | (have i₁ := eq56 X0 sF4
       have i₂ := eq1899867 sF4 x
       grind)
    | exact superpose eq1899867 eq56
    | (have j1 := eq1899867 X1 x
       grind)
    | exact resolve eq56 eq1899867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899867
  have eq1911132 : ∀ X0 X1 : G, (M.op X1 X1) = y ∨ (M.op X0 X0) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq28 eq1910308
    | (have j0 := eq1910308 X0 X1
       grind)
    | exact resolve eq1910308 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1910308
  have eq1914760 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1900075 eq51
    | exact resolve eq51 eq1900075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1914777 : (σ y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1900075 eq1100843
    | exact resolve eq1100843 eq1900075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100843 eq1900075
  have eq1914817 : (σ y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1914777
  have eq1914836 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (k x x) := by
    first
    | exact superpose eq31 eq1914760
    | exact resolve eq1914760 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914760
  have eq1917241 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq143017 sF0 X1
       have i₂ := eq1906442 X0 sF0
       grind)
    | exact superpose eq1906442 eq143017
    | (have j1 := eq1906442 X1 x
       grind)
    | exact resolve eq143017 eq1906442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906442
  have eq1918053 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq1917241 X0 X1
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1917241
    | (have j0 := eq1917241 X0 X1
       grind)
    | exact resolve eq1917241 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917241
  have eq1918291 : ∀ X0 X1 : G, (M.op X1 X1) = y ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq22 eq1918053
    | (have j0 := eq1918053 X0 X1
       grind)
    | exact resolve eq1918053 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1918053
  have eq1927728 : ∀ X0 X3 : G, (M.op X0 X0) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op X3 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq143084 x x (k x (M.op x x)) X0
       have i₂ := eq1911132 X3 (k x (M.op x x))
       grind)
    | exact superpose eq1911132 eq143084
    | (have j1 := eq1911132 X3 x
       grind)
    | exact resolve eq143084 eq1911132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143084 eq1911132
  have eq1927777 : ∀ X0 X3 : G, (M.op (σ x) (σ y)) = (M.op X3 X3) ∨ (M.op X0 X0) = (σ y) := by
    intro X0 X3
    first
    | (have i₁ := eq1927728 X0 X3
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq1927728
    | (have j0 := eq1927728 X0 X3
       grind)
    | exact resolve eq1927728 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927728
  have eq1928169 : ∀ X0 : G, y = (k x x) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1914836
       have i₂ := eq59 sF2 x
       grind)
    | (have i₁ := eq1914836
       have i₂ := eq59 X0 sF2
       grind)
    | exact superpose eq59 eq1914836
    | exact resolve eq1914836 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914836
  have eq1939899 : ∀ X1 : G, y = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X1 X1) = (σ (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq75050 x
       have i₂ := eq1918291 X1 x
       grind)
    | exact superpose eq1918291 eq75050
    | (have j1 := eq1918291 (σ (M.op x y)) X1
       grind)
    | exact resolve eq75050 eq1918291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75050 eq1918291
  have eq1942143 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j0 := eq1939899 (σ (M.op x y))
       grind)
    | (have r₁ := eq1939899 x
       have r₂ := eq623328 (σ (M.op x y))
       grind)
    | (have r₁ := eq1939899 x
       have r₂ := eq623328 x
       grind)
    | exact resolve eq1939899 eq623328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623328 eq1939899
  have eq1950014 : ∀ X0 : G, y = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1914817
       have i₂ := eq1928169 X0
       grind)
    | exact superpose eq1928169 eq1914817
    | (have j1 := eq1928169 (σ x)
       grind)
    | exact resolve eq1914817 eq1928169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914817 eq1928169
  have eq1950069 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (σ y) := by
    first
    | (have j0 := eq1950014 (σ x)
       grind)
    | (have r₁ := eq1950014 x
       have r₂ := eq627524 (σ x)
       grind)
    | (have r₁ := eq1950014 x
       have r₂ := eq627524 x
       grind)
    | exact resolve eq1950014 eq627524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627524 eq1950014
  have eq1950137 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1950069
       have i₂ := eq59 sF2 x
       grind)
    | (have i₁ := eq1950069
       have i₂ := eq59 X0 sF2
       grind)
    | exact superpose eq59 eq1950069
    | exact resolve eq1950069 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1950449 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq1950069 eq140774
    | exact resolve eq140774 eq1950069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140774
  have eq1951072 : ∀ X0 : G, (M.op X0 X0) = x ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq30 eq1950449
    | exact resolve eq1950449 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950449
  have eq1960892 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq56 X0 sF4
       have i₂ := eq1950137 sF4
       grind)
    | exact superpose eq1950137 eq56
    | exact resolve eq56 eq1950137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1950137
  have eq1961725 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq28 eq1960892
    | (have j0 := eq1960892 X0
       grind)
    | exact resolve eq1960892 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1960892
  have eq1969039 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq143017 sF0 x
       have i₂ := eq1951072 sF0
       grind)
    | exact superpose eq1951072 eq143017
    | exact resolve eq143017 eq1951072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143017 eq1951072
  have eq1969866 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1969039 X0
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq1969039
    | (have j0 := eq1969039 X0
       grind)
    | exact resolve eq1969039 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969039
  have eq1970103 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq22 eq1969866
    | (have j0 := eq1969866 X0
       grind)
    | exact resolve eq1969866 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969866
  have eq1979457 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq1950069
       have i₂ := eq1961725 sF2
       grind)
    | exact superpose eq1961725 eq1950069
    | exact resolve eq1950069 eq1961725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961725
  have eq1979467 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq1979457
  have eq1984449 : (σ (M.op x y)) ≠ (σ x) ∨ y = (σ y) := by
    first
    | exact superpose eq1979467 eq29
    | exact resolve eq29 eq1979467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979467
  have eq2008239 : (σ (M.op x y)) = (σ x) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq1950069
       have i₂ := eq1970103 sF2
       grind)
    | exact superpose eq1970103 eq1950069
    | exact resolve eq1950069 eq1970103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950069 eq1970103
  have eq2008249 : (σ (M.op x y)) = (σ x) ∨ y = (σ y) := by grind
  clear eq2008239
  have eq2008269 : y = (σ y) := by
    first
    | (have r₁ := eq2008249
       have r₂ := eq1984449
       grind)
    | exact resolve eq2008249 eq1984449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1984449 eq2008249
  have eq2008504 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq2008269 eq28
    | exact resolve eq28 eq2008269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2008505 : y = (τ y) := by
    first
    | exact superpose eq2008269 eq31
    | exact resolve eq31 eq2008269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2480489 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = (σ y) ∨ y = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1942143 eq1927777
    | (have j0 := eq1927777 X0 x
       grind)
    | exact resolve eq1927777 eq1942143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927777 eq1942143
  have eq2480680 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ y = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq2480489 X0
       grind)
    | (have r₁ := eq2480489 X0
       have r₂ := eq29
       grind)
    | exact resolve eq2480489 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480489
  have eq2480844 : ∀ X0 : G, y = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq2008269 eq2480680
    | exact resolve eq2480680 eq2008269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480680
  have eq2525366 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq2480844 eq195
    | (have j1 := eq2480844 X0
       grind)
    | exact resolve eq195 eq2480844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195 eq2480844
  have eq2525442 : ∀ X0 : G, y = (k (M.op x y) (M.op x y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq2525366 X0
       have i₂ := eq2008505
       grind)
    | exact superpose eq2008505 eq2525366
    | (have j0 := eq2525366 X0
       grind)
    | exact resolve eq2525366 eq2008505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525366
  have eq3753079 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op x y)) ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | exact superpose eq2008269 eq1896733
    | (have j0 := eq1896733 X0 X1
       grind)
    | exact resolve eq1896733 eq2008269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896733
  have eq3770570 : ∀ X0 X2 : G, (τ (M.op X0 X0)) = (σ (τ (M.op x y))) ∨ y = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq174552 x (τ (M.op x x)) X0
       have i₂ := eq3753079 (τ (M.op x x)) X2
       grind)
    | (have i₁ := eq174552 X0 (τ (M.op X0 X0)) x
       have i₂ := eq3753079 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq3753079 eq174552
    | (have j1 := eq3753079 X0 X2
       grind)
    | exact resolve eq174552 eq3753079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174552 eq3753079
  have eq3770775 : ∀ X0 X2 : G, (M.op x y) = (τ (M.op X0 X0)) ∨ y = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq3770570 X0 X2
       have i₂ := eq15 sF0
       grind)
    | exact superpose eq15 eq3770570
    | (have j0 := eq3770570 X0 X2
       grind)
    | exact resolve eq3770570 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3770570
  have eq3842476 : ∀ X1 : G, (M.op x y) = (τ (k (σ y) (σ y))) ∨ (M.op X1 X1) = y ∨ y = (M.op y y) := by
    intro X1
    first
    | (have i₁ := eq3770775 x X1
       have i₂ := eq632236 x
       grind)
    | (have i₁ := eq3770775 y x
       have i₂ := eq632236 x
       grind)
    | exact superpose eq632236 eq3770775
    | (have j0 := eq3770775 x X1
       grind)
    | exact resolve eq3770775 eq632236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632236 eq3770775
  have eq3843601 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have j0 := eq3842476 y
       have j1 := eq629984 x y
       grind)
    | (have r₁ := eq3842476 x
       have r₂ := eq629984 x y
       grind)
    | (have r₁ := eq3842476 x
       have r₂ := eq629984 y y
       grind)
    | exact resolve eq3842476 eq629984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3842476
  have eq3843688 : (M.op x y) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq132 eq3843601
    | exact resolve eq3843601 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq3843601
  have eq3843754 : ∀ X0 : G, (σ y) ≠ (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq1103202 X0
       have i₂ := eq3843688
       grind)
    | exact superpose eq3843688 eq1103202
    | exact resolve eq1103202 eq3843688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103202 eq3843688
  have eq3843877 : ∀ X0 : G, y ≠ (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2008269 eq3843754
    | exact resolve eq3843754 eq2008269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843754
  have eq3843912 : ∀ X0 : G, y = (M.op y y) ∨ y ≠ (k X0 (M.op x y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq2008269 eq3843877
    | (have j0 := eq3843877 X0
       grind)
    | exact resolve eq3843877 eq2008269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843877
  have eq3843913 : ∀ X0 : G, y ≠ (k X0 (M.op x y)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq3843912 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3843912
  have eq3898009 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq2525442 eq3843913
    | (have j1 := eq2525442 y
       grind)
    | (have r₁ := eq3843913 (M.op x y)
       have r₂ := eq2525442 X0
       grind)
    | exact resolve eq3843913 eq2525442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2525442 eq3843913
  have eq3898051 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq3898009 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898009
  have eq3898053 : y = (M.op y y) := by
    first
    | (have j0 := eq3898051 y
       have j1 := eq629984 x y
       grind)
    | (have r₁ := eq3898051 x
       have r₂ := eq629984 y y
       grind)
    | (have r₁ := eq3898051 x
       have r₂ := eq629984 x y
       grind)
    | exact resolve eq3898051 eq629984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629984 eq3898051
  have eq3898064 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq3898053
       have i₂ := eq59 y X0
       grind)
    | (have i₁ := eq3898053
       have i₂ := eq59 X0 y
       grind)
    | exact superpose eq59 eq3898053
    | exact resolve eq3898053 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq3898053
  have eq3904064 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op y X3) := by
    intro X0 X3
    first
    | (have i₁ := eq18549 x X0 x (k x (k x (M.op x x))) X3
       have i₂ := eq3898064 (k x (k x (M.op x x)))
       grind)
    | exact superpose eq3898064 eq18549
    | exact resolve eq18549 eq3898064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18549
  have eq3904065 : ∀ X0 : G, y = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq17143 x X0 x (k x (k x (M.op x x)))
       have i₂ := eq3898064 (k x (k x (M.op x x)))
       grind)
    | exact superpose eq3898064 eq17143
    | exact resolve eq17143 eq3898064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17143
  have eq3904150 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq3904065 X0
       have i₂ := eq3898064 X0
       grind)
    | exact superpose eq3898064 eq3904065
    | exact resolve eq3904065 eq3898064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904065
  have eq3904151 : ∀ X3 : G, y = (M.op y X3) := by
    intro X3
    first
    | (have i₁ := eq3904064 x X3
       have i₂ := eq3898064 x
       grind)
    | exact superpose eq3898064 eq3904064
    | exact resolve eq3904064 eq3898064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904064
  have eq3948497 : ∀ X0 X1 X6 X7 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op (k X0 y) X6) X7) := by
    intro X0 X1 X6 X7
    first
    | (have i₁ := eq47309 X0 X1 X6 X7
       have i₂ := eq3898064 X0
       grind)
    | exact superpose eq3898064 eq47309
    | exact resolve eq47309 eq3898064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47309
  have eq3948498 : ∀ X1 X6 X7 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op y X6) X7) := by
    intro X1 X6 X7
    first
    | (have i₁ := eq3948497 x X1 X6 X7
       have i₂ := eq3904150 x
       grind)
    | exact superpose eq3904150 eq3948497
    | exact resolve eq3948497 eq3904150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948497
  have eq3948499 : ∀ X1 X7 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) = (M.op y X7) := by
    intro X1 X7
    first
    | (have i₁ := eq3948498 X1 x X7
       have i₂ := eq3904151 x
       grind)
    | exact superpose eq3904151 eq3948498
    | exact resolve eq3948498 eq3904151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948498
  have eq3948500 : ∀ X1 : G, y = (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq3948499 X1 x
       have i₂ := eq3904151 x
       grind)
    | exact superpose eq3904151 eq3948499
    | exact resolve eq3948499 eq3904151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904151 eq3948499
  have eq3948501 : ∀ X1 : G, y = (M.op (M.op X1 (M.op (σ x) (σ y))) y) := by
    intro X1
    first
    | exact superpose eq2008269 eq3948500
    | exact resolve eq3948500 eq2008269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3948500
  have eq3949738 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq3948501 eq2294
    | exact resolve eq2294 eq3948501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294 eq3948501
  have eq3950082 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq3949738 X0
       have i₂ := eq3904150 X0
       grind)
    | exact superpose eq3904150 eq3949738
    | (have j0 := eq3949738 X0
       grind)
    | exact resolve eq3949738 eq3904150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904150 eq3949738
  have eq4019961 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq116
       have i₂ := eq3950082 x
       grind)
    | exact superpose eq3950082 eq116
    | (have j1 := eq3950082 x
       grind)
    | exact resolve eq116 eq3950082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq4020017 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq2008269 eq4019961
    | exact resolve eq4019961 eq2008269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4019961
  have eq4020114 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq4020017
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq4020017
    | exact resolve eq4020017 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4020017
  have eq4020188 : (σ (M.op x y)) = (k y (σ x)) ∨ x = y := by
    first
    | exact superpose eq22 eq4020114
    | exact resolve eq4020114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4020114
  have eq4020261 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq4020188 eq3950082
    | (have j0 := eq3950082 (σ x)
       grind)
    | exact resolve eq3950082 eq4020188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3950082 eq4020188
  have eq4020277 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ x) ∨ x = y := by
    first
    | exact superpose eq2008504 eq4020261
    | exact resolve eq4020261 eq2008504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008504 eq4020261
  have eq4020292 : y = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq4020277
       have r₂ := eq29
       grind)
    | exact resolve eq4020277 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4020277
  have eq4020306 : x = (τ y) ∨ x = y := by
    first
    | exact superpose eq4020292 eq30
    | exact resolve eq30 eq4020292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4020292
  have eq4020495 : x = y ∨ x = y := by
    first
    | (have i₁ := eq4020306
       have i₂ := eq2008505
       grind)
    | exact superpose eq2008505 eq4020306
    | exact resolve eq4020306 eq2008505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008505 eq4020306
  have eq4020496 : x = y := by grind
  clear eq4020495
  have eq4020609 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq4020496
       grind)
    | exact superpose eq4020496 eq20
    | exact resolve eq20 eq4020496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4020610 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq4020496
       grind)
    | exact superpose eq4020496 eq26
    | exact resolve eq26 eq4020496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4021446 : y = (σ x) := by
    first
    | exact superpose eq2008269 eq4020610
    | exact resolve eq4020610 eq2008269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4020610
  have eq4021447 : y = (M.op x y) := by
    first
    | (have i₁ := eq4020609
       have i₂ := eq3898064 x
       grind)
    | exact superpose eq3898064 eq4020609
    | exact resolve eq4020609 eq3898064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3898064 eq4020609
  have eq4021765 : y = (σ x) := by
    first
    | (have i₁ := eq4021446
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4021446
    | exact resolve eq4021446 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021446
  have eq4021766 : x = (M.op x y) := by
    first
    | (have i₁ := eq4021447
       have i₂ := eq4020496
       grind)
    | exact superpose eq4020496 eq4021447
    | exact resolve eq4021447 eq4020496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021447
  have eq4021998 : x = (σ x) := by
    first
    | (have i₁ := eq4021765
       have i₂ := eq4020496
       grind)
    | exact superpose eq4020496 eq4021765
    | exact resolve eq4021765 eq4020496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4020496 eq4021765
  have eq4022202 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq4021766 eq22
    | exact resolve eq22 eq4021766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4022760 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4022202
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4022202
    | exact resolve eq4022202 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4022202
  have eq4023398 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq4021998 eq28
    | exact resolve eq28 eq4021998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq4023585 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2008269 eq4023398
    | exact resolve eq4023398 eq2008269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008269 eq4023398
  have eq4023625 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4023585
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq4023585
    | exact resolve eq4023585 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4023585
  have eq4023646 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4021766 eq4023625
    | exact resolve eq4023625 eq4021766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021766 eq4023625
  have eq4023654 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq4021998 eq4022760
    | exact resolve eq4022760 eq4021998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4021998 eq4022760
  have eq4023657 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq4023646 eq29
    | exact resolve eq29 eq4023646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4023646
  have eq4024790 : False := by grind
  exact eq4024790
