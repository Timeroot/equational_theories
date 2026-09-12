import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_pyy_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
    intro X0 X1 X2
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
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op x X1)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : (M.op x y) ≠ (M.op x x) ∨ (M.op y x) = (k y x) := by
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
  have eq64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq10
    | exact resolve eq10 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq43
    | exact resolve eq43 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq69 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq49
    | exact resolve eq49 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq70 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq69
       have i₂ := eq65 x
       grind)
    | exact superpose eq65 eq69
    | exact resolve eq69 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq71 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq67
    | exact resolve eq67 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq99 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq100 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24
  have eq102 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (M.op (σ y) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq11 sF3 (σ X0)
       grind)
    | exact superpose eq11 eq36
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq36 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq104 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq65 sF3
       grind)
    | exact superpose eq65 eq100
    | exact resolve eq100 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq65 y
       grind)
    | exact superpose eq65 eq104
    | exact resolve eq104 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq104
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq99
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq16
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq245 : (M.op y x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq53
    | (have j0 := eq53 x y
       grind)
    | exact resolve eq53 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq53
    | (have j0 := eq53 (σ x) (σ y)
       grind)
    | exact resolve eq53 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5789 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ y)) ∨ (M.op (σ X0) (σ y)) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq102 X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq102
    | (have j0 := eq102 X0
       grind)
    | exact resolve eq102 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq102
  have eq5970 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5789 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5789
    | (have j0 := eq5789 x
       grind)
    | exact resolve eq5789 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5789
  have eq5990 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5970
       have i₂ := eq99
       grind)
    | exact superpose eq99 eq5970
    | exact resolve eq5970 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5970
  have eq6012 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq5990
    | exact resolve eq5990 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5990
  have eq6025 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq6012
       have i₂ := eq71
       grind)
    | exact superpose eq71 eq6012
    | exact resolve eq6012 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6012
  have eq6032 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq6025
    | exact resolve eq6025 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6025
  have eq6039 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq6032
    | exact resolve eq6032 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6032
  have eq15900 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq15900
    | exact resolve eq15900 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15900
  have eq15912 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq15901
       have r₂ := eq27
       grind)
    | exact resolve eq15901 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15901
  have eq15916 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq15912
    | exact resolve eq15912 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15912
  have eq15918 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq15916
    | exact resolve eq15916 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15916
  have eq15925 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq15918 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15918
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15918
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15918
       grind)
    | exact resolve eq12 eq15918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15918
  have eq15943 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq15925
       have r₂ := eq26
       grind)
    | exact resolve eq15925 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15925
  have eq15945 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq15943
    | exact resolve eq15943 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15943
  have eq15946 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq15945
  have eq16506 : (k y x) = (τ (M.op (σ x) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq15946 eq113
    | exact resolve eq113 eq15946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq15946
  have eq16527 : (M.op x x) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq70 eq16506
    | exact resolve eq16506 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq16506
  have eq16797 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq16527
       grind)
    | exact superpose eq16527 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq16527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16527
  have eq16798 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq16797
  have eq16800 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16798
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16798
    | exact resolve eq16798 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16798
  have eq16801 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq16800
  have eq16813 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16801
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16801
    | exact resolve eq16801 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16801
  have eq16814 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq16813
  have eq16817 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq16814 eq64
    | (have r₁ := eq64
       have r₂ := eq16814
       grind)
    | exact resolve eq64 eq16814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq16835 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq16814 eq53
    | exact resolve eq53 eq16814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16814
  have eq16845 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq16817
  have eq16846 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq246 eq16835
    | exact resolve eq16835 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq16835
  have eq17486 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq16845 eq117
    | exact resolve eq117 eq16845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq16845
  have eq17497 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq17486
  have eq17513 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq17497 eq16846
    | exact resolve eq16846 eq17497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16846 eq17497
  have eq17526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq17513
  have eq17539 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq17526
       have r₂ := eq27
       grind)
    | exact resolve eq17526 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17526
  have eq17551 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op (M.op x y) X0) x) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq17539
       grind)
    | exact superpose eq17539 eq14
    | exact resolve eq14 eq17539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19056 : (M.op x x) = (M.op (M.op y x) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq245 eq17551
    | exact resolve eq17551 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17551
  have eq19531 : (M.op x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19056
       have i₂ := eq17539
       grind)
    | exact superpose eq17539 eq19056
    | exact resolve eq19056 eq17539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19056
  have eq19550 : (M.op x x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq19531
  have eq19552 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq245 eq19550
    | exact resolve eq19550 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19550
  have eq19560 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq17539
       have i₂ := eq19552
       grind)
    | exact superpose eq19552 eq17539
    | exact resolve eq17539 eq19552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17539 eq19552
  have eq19577 : (M.op x y) = (M.op x x) := by grind
  clear eq19560
  have eq19594 : (M.op x y) ≠ (M.op x y) ∨ (M.op y x) = (k y x) := by
    first
    | (have i₁ := eq63
       have i₂ := eq19577
       grind)
    | exact superpose eq19577 eq63
    | (have r₁ := eq63
       have r₂ := eq19577
       grind)
    | exact resolve eq63 eq19577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq19595 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq19577
       grind)
    | exact superpose eq19577 eq71
    | exact resolve eq71 eq19577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq19612 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq53 x x
       have i₂ := eq19577
       grind)
    | exact superpose eq19577 eq53
    | exact resolve eq53 eq19577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19577
  have eq19624 : (M.op y x) = (k y x) := by grind
  clear eq19594
  have eq19625 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq245 eq19612
    | exact resolve eq19612 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq19612
  have eq19638 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq19595
    | exact resolve eq19595 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19595
  have eq19655 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq53 y x
       have i₂ := eq19625
       grind)
    | exact superpose eq19625 eq53
    | exact resolve eq53 eq19625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19675 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq19655
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq19655
    | exact resolve eq19655 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19655
  have eq20025 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq19675 eq50
    | exact resolve eq50 eq19675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq20044 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq19675 eq20025
    | exact resolve eq20025 eq19675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19675 eq20025
  have eq20085 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq20044
       grind)
    | exact superpose eq20044 eq106
    | exact resolve eq106 eq20044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq20044
  have eq20136 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq20085
    | exact resolve eq20085 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20085
  have eq20372 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq19624
       have i₂ := eq19625
       grind)
    | exact superpose eq19625 eq19624
    | exact resolve eq19624 eq19625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19624 eq19625
  have eq20376 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq99
       have i₂ := eq20372
       grind)
    | exact superpose eq20372 eq99
    | exact resolve eq99 eq20372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq20372
  have eq20402 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq20376
    | exact resolve eq20376 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq20376
  have eq20481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq20402 eq6039
    | exact resolve eq6039 eq20402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6039 eq20402
  have eq20487 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq20481
       have r₂ := eq27
       grind)
    | exact resolve eq20481 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20481
  have eq20500 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq19638 eq20487
    | exact resolve eq20487 eq19638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19638 eq20487
  have eq20506 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq20500
       have r₂ := eq27
       grind)
    | exact resolve eq20500 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20500
  have eq20527 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq20506 eq53
    | exact resolve eq53 eq20506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq20506
  have eq20549 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq20527
    | exact resolve eq20527 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq20527
  have eq20623 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq20549 eq51
    | exact resolve eq51 eq20549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq20646 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20549 eq20623
    | exact resolve eq20623 eq20549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20549 eq20623
  have eq20652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20136 eq20646
    | exact resolve eq20646 eq20136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20136 eq20646
  have eq20654 : False := by grind
  exact eq20654

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_y_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq24 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq18
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (M.op x y)) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq54 (σ x) (σ y)
       grind)
    | exact superpose eq54 eq16
    | (have j1 := eq54 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq54 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq13 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X1 X2) ∨ (k X0 X2) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X0
       have i₂ := eq54 X0 X2
       grind)
    | exact superpose eq54 eq9
    | (have j1 := eq54 X0 X2
       grind)
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq54 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq54 X1 X1
       grind)
    | exact resolve eq12 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq73 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq75 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq66
    | exact resolve eq66 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq76 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq54 x y
       grind)
    | exact superpose eq54 eq75
    | (have j1 := eq54 x y
       grind)
    | exact resolve eq75 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : (k x y) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
  clear eq76
  have eq91 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq24
    | (have j1 := eq54 X0 X1
       grind)
    | exact resolve eq24 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X1 X0) X1
       have i₂ := eq24 X1 X0
       grind)
    | exact superpose eq24 eq24
    | exact resolve eq24 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq74 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq74
    | exact resolve eq74 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 X0
       have i₂ := eq74 (σ X1) X0
       grind)
    | exact superpose eq74 eq30
    | (have j1 := eq74 (σ X1) X0
       grind)
    | exact resolve eq30 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq125 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq74 (τ X1) X0
       grind)
    | exact superpose eq74 eq17
    | (have j1 := eq74 (τ X1) X0
       grind)
    | exact resolve eq17 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq168 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq72 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq169 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq168 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq187 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq169 (τ X0)
       grind)
    | exact superpose eq169 eq17
    | exact resolve eq17 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq187 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq187
    | exact resolve eq187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq199 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq169 X0
       grind)
    | exact superpose eq169 eq188
    | exact resolve eq188 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq188
  have eq207 : ∀ X0 X1 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X1 X2) = (M.op X0 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq54 X0 X1
       grind)
    | exact superpose eq54 eq68
    | (have j0 := eq68 X0 X1 X2
       have j1 := eq54 X0 X2
       grind)
    | exact resolve eq68 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq219 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq199 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq199
    | exact resolve eq199 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq330 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq125 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq125
    | exact resolve eq125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq125 X0 X1
       grind)
    | exact superpose eq125 eq17
    | (have j1 := eq125 X0 X1
       grind)
    | exact resolve eq17 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq125
  have eq358 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq330 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq330
    | (have j0 := eq330 X0 X1
       grind)
    | exact resolve eq330 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq377 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq24 (σ X0) (σ X0)
       have i₂ := eq219 X0
       grind)
    | exact superpose eq219 eq24
    | exact resolve eq24 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq579 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq92 (σ X0) (σ X0)
       have i₂ := eq219 X0
       grind)
    | exact superpose eq219 eq92
    | exact resolve eq92 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq607 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq579 X0
       have i₂ := eq219 (M.op X0 X0)
       grind)
    | exact superpose eq219 eq579
    | exact resolve eq579 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq615 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq607 X0
       have i₂ := eq92 X0 X0
       grind)
    | exact superpose eq92 eq607
    | exact resolve eq607 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq607
  have eq807 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq114 x y
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq114
    | (have j0 := eq114 x y
       grind)
    | exact resolve eq114 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq114 X1 X0
       grind)
    | exact superpose eq114 eq10
    | (have j1 := eq114 X1 X0
       grind)
    | exact resolve eq10 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq842 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq812 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq812
    | (have j0 := eq812 X0 X1
       grind)
    | exact resolve eq812 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq1425 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1426 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq2080 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq842 x y
       grind)
    | exact superpose eq842 eq16
    | (have j1 := eq842 x y
       grind)
    | exact resolve eq16 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq2146 : x = (k y x) := by
    first
    | (have j1 := eq358 y x
       grind)
    | (have r₁ := eq2080
       have r₂ := eq358 y x
       grind)
    | exact resolve eq2080 eq358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq2080
  have eq2184 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq2146
       have i₂ := eq91 y x
       grind)
    | exact superpose eq91 eq2146
    | (have j1 := eq91 y x
       grind)
    | exact resolve eq2146 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2221 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq123 (σ X0) X1
       grind)
    | exact superpose eq123 eq22
    | (have j1 := eq123 (σ X0) X1
       grind)
    | exact resolve eq22 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq123
  have eq2228 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2221 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2221
    | (have j0 := eq2221 X0 X1
       grind)
    | exact resolve eq2221 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq2247 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2228 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2228
    | (have j0 := eq2228 X0 X1
       grind)
    | exact resolve eq2228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2228
  have eq2255 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2247 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2247
    | (have j0 := eq2247 X0 X1
       grind)
    | exact resolve eq2247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247
  have eq2375 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq338
    | (have j0 := eq338 X1 (σ X0)
       grind)
    | exact resolve eq338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq2442 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ X1) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2375 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2375
    | (have j0 := eq2375 X0 X1
       grind)
    | exact resolve eq2375 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq2453 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2442 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2442
    | (have j0 := eq2442 X0 X1
       grind)
    | exact resolve eq2442 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442
  have eq4069 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 X0) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2255 X0 X1
       have i₂ := eq54 (σ X0) (σ X1)
       grind)
    | exact superpose eq54 eq2255
    | (have j0 := eq2255 X0 X1
       have j1 := eq54 (σ X0) (σ X1)
       grind)
    | exact resolve eq2255 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2255
  have eq4127 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4069 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4069
    | (have j0 := eq4069 X0 X1
       grind)
    | exact resolve eq4069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4069
  have eq4128 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq4127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4127
  have eq4137 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4128 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4128
    | (have j0 := eq4128 X0 X1
       grind)
    | exact resolve eq4128 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4128
  have eq4968 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4137 y x
       grind)
    | exact superpose eq4137 eq16
    | (have j1 := eq4137 y x
       grind)
    | exact resolve eq16 eq4137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4137
  have eq5041 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k x y) := by
    first
    | (have i₁ := eq4968
       have i₂ := eq2146
       grind)
    | exact superpose eq2146 eq4968
    | exact resolve eq4968 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4968
  have eq5199 : (σ x) ≠ (σ x) ∨ y = (k x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq5041
       have i₂ := eq2184
       grind)
    | exact superpose eq2184 eq5041
    | exact resolve eq5041 eq2184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184 eq5041
  have eq5202 : y = (k x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq5199
  have eq7983 : ∀ X0 X1 : G, (σ X1) ≠ (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq2453 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453
  have eq16685 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op y x)) ∨ (σ y) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq807
       have i₂ := eq54 (σ y) (σ x)
       grind)
    | exact superpose eq54 eq807
    | (have j1 := eq54 (σ y) (σ x)
       grind)
    | exact resolve eq807 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq16736 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq16685
  have eq16763 : (σ y) = (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq7983 x y
       grind)
    | (have r₁ := eq16736
       have r₂ := eq7983 x y
       grind)
    | exact resolve eq16736 eq7983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7983 eq16736
  have eq16768 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16763
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq16763
    | exact resolve eq16763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16763
  have eq16770 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16768
       have i₂ := eq2146
       grind)
    | exact superpose eq2146 eq16768
    | exact resolve eq16768 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16768
  have eq16775 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16770
       grind)
    | exact superpose eq16770 eq16
    | exact resolve eq16 eq16770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16770
  have eq20237 : (M.op y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1426 y x
       have i₂ := eq2146
       grind)
    | exact superpose eq2146 eq1426
    | (have j0 := eq1426 y x
       grind)
    | exact resolve eq1426 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20330 : y = (M.op y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq5202
       have i₂ := eq1426 x y
       grind)
    | exact superpose eq1426 eq5202
    | (have j1 := eq1426 x y
       grind)
    | exact resolve eq5202 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426 eq5202
  have eq20333 : y = (M.op y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq20330
  have eq20395 : y = (M.op x x) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54 y x
       have i₂ := eq20237
       grind)
    | exact superpose eq20237 eq54
    | (have j0 := eq54 x y
       grind)
    | exact resolve eq54 eq20237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq20237
  have eq20423 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20395
       have i₂ := eq2146
       grind)
    | exact superpose eq2146 eq20395
    | exact resolve eq20395 eq2146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146 eq20395
  have eq20424 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq20423
  have eq20664 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16775
       have i₂ := eq20424
       grind)
    | exact superpose eq20424 eq16775
    | exact resolve eq16775 eq20424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16775
  have eq20669 : (M.op y x) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24 x y
       have i₂ := eq20424
       grind)
    | exact superpose eq20424 eq24
    | exact resolve eq24 eq20424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20424
  have eq20702 : y = (M.op x x) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq20664
  have eq22147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq615 x
       have i₂ := eq20702
       grind)
    | exact superpose eq20702 eq615
    | exact resolve eq615 eq20702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq20702
  have eq22202 : (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq22147
       have r₂ := eq16
       grind)
    | exact resolve eq22147 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22147
  have eq22368 : (k x y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq22202
       grind)
    | exact superpose eq22202 eq10
    | exact resolve eq10 eq22202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22202
  have eq22465 : y = (k x y) := by
    first
    | (have i₁ := eq22368
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq22368
    | exact resolve eq22368 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22368
  have eq22605 : y = (M.op y x) ∨ (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq22465
       have i₂ := eq91 x y
       grind)
    | exact superpose eq91 eq22465
    | (have j1 := eq91 x y
       grind)
    | exact resolve eq22465 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq22607 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq22465
       grind)
    | exact superpose eq22465 eq77
    | exact resolve eq77 eq22465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq22465
  have eq24404 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq24 y x
       have i₂ := eq20333
       grind)
    | exact superpose eq20333 eq24
    | exact resolve eq24 eq20333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20333
  have eq24446 : (M.op x y) = (M.op y y) := by grind
  clear eq24404
  have eq27378 : y ≠ (M.op x x) ∨ (M.op y x) = (M.op x x) := by grind
  clear eq22605
  have eq27384 : (M.op y x) = (M.op x x) := by
    first
    | (have r₁ := eq27378
       have r₂ := eq20669
       grind)
    | exact resolve eq27378 eq20669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20669 eq27378
  have eq30310 : y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq22607
       have i₂ := eq27384
       grind)
    | exact superpose eq27384 eq22607
    | exact resolve eq22607 eq27384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22607 eq27384
  have eq31719 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq377 x
       have i₂ := eq30310
       grind)
    | exact superpose eq30310 eq377
    | exact resolve eq377 eq30310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq30310
  have eq31794 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq31719
  have eq32278 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq24 (σ y) (σ x)
       have i₂ := eq31794
       grind)
    | exact superpose eq31794 eq24
    | exact resolve eq24 eq31794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31794
  have eq32360 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq32278
       have i₂ := eq219 y
       grind)
    | exact superpose eq219 eq32278
    | exact resolve eq32278 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq32278
  have eq32398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32360
       have i₂ := eq24446
       grind)
    | exact superpose eq24446 eq32360
    | exact resolve eq32360 eq24446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24446 eq32360
  have eq32426 : False := by grind
  exact eq32426

/-- `Equation4209`: `x ◇ y = ((z ◇ y) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxy_pyx_Equation4209 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4209 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4209.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X1) X0) X1) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x X1)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq15
    | exact resolve eq15 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq53 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq50 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq50
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq48
    | exact resolve eq48 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq53
    | exact resolve eq53 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq53
  have eq78 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq78
    | (have j0 := eq78 X0 X1
       grind)
    | exact resolve eq78 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq87 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0) (σ X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq20
    | exact resolve eq20 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq87
    | (have j0 := eq87 X1 X1
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq134 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq119
    | (have j0 := eq119 X0 X1
       grind)
    | exact resolve eq119 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq141 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq134 X0 X1
       have j1 := eq96 X1 X0
       grind)
    | (have r₁ := eq134 X0 X0
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq134 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq915 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq141 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141
    | exact resolve eq141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq141 (σ X1) X0
       grind)
    | exact superpose eq141 eq15
    | (have j1 := eq141 (σ X1) X0
       grind)
    | exact resolve eq15 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq946 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq915 X0 X1
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq915
    | (have j0 := eq915 X0 X1
       grind)
    | exact resolve eq915 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq915
  have eq971 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq946 X0 (τ X1)
       grind)
    | exact superpose eq946 eq17
    | (have j1 := eq946 X0 (τ X1)
       grind)
    | exact resolve eq17 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq946
  have eq3893 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq971 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq971
    | exact resolve eq971 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971
  have eq3982 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3893 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3893
    | (have j0 := eq3893 X0 X1
       grind)
    | exact resolve eq3893 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq9372 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq928 x y
       grind)
    | exact superpose eq928 eq16
    | (have j1 := eq928 x y
       grind)
    | exact resolve eq16 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9436 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq928 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq9772 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq9372
       have i₂ := eq3982 y x
       grind)
    | exact superpose eq3982 eq9372
    | (have j1 := eq3982 y x
       grind)
    | (have r₁ := eq9372
       have r₂ := eq3982 y x
       grind)
    | exact resolve eq9372 eq3982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3982 eq9372
  have eq9773 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq9772
  have eq9777 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op y x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq9773
       grind)
    | exact superpose eq9773 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9773
       grind)
    | exact resolve eq13 eq9773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9778 : (M.op y x) = (M.op (M.op x x) x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq20 x y
       have i₂ := eq9773
       grind)
    | exact superpose eq9773 eq20
    | exact resolve eq20 eq9773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9773
  have eq9793 : (k y x) = (M.op y x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq9777
  have eq9794 : (M.op x x) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9778
       have i₂ := eq20 x x
       grind)
    | exact superpose eq20 eq9778
    | exact resolve eq9778 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9778
  have eq44816 : (σ (M.op x x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9436 x y
       have i₂ := eq9793
       grind)
    | exact superpose eq9793 eq9436
    | (have j0 := eq9436 x y
       grind)
    | exact resolve eq9436 eq9793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9436 eq9793
  have eq44825 : (σ (M.op x x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq44816
  have eq190376 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44825
       have i₂ := eq9794
       grind)
    | exact superpose eq9794 eq44825
    | exact resolve eq44825 eq9794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9794 eq44825
  have eq190377 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq190376
  have eq190378 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq190377
  have eq190381 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq190378
       grind)
    | exact superpose eq190378 eq16
    | exact resolve eq16 eq190378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190394 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (σ (M.op x x)) X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (σ y) (σ x)
       have i₂ := eq190378
       grind)
    | exact superpose eq190378 eq9
    | exact resolve eq9 eq190378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190396 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 (σ x) (σ y)
       have i₂ := eq190378
       grind)
    | exact superpose eq190378 eq20
    | exact resolve eq20 eq190378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190492 : (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq190396
       have i₂ := eq93 x
       grind)
    | exact superpose eq93 eq190396
    | exact resolve eq190396 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq190396
  have eq191464 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 (σ y) (σ x)
       have i₂ := eq190492
       grind)
    | exact superpose eq190492 eq20
    | exact resolve eq20 eq190492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190492
  have eq192994 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq190394 (σ y)
       have i₂ := eq191464
       grind)
    | exact superpose eq191464 eq190394
    | exact resolve eq190394 eq191464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190394
  have eq193103 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq192994
  have eq193130 : (σ (M.op y y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq193103
       have i₂ := eq55 y
       grind)
    | exact superpose eq55 eq193103
    | exact resolve eq193103 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq193103
  have eq194231 : (σ (M.op y y)) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq193130
       have i₂ := eq190378
       grind)
    | exact superpose eq190378 eq193130
    | exact resolve eq193130 eq190378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193130
  have eq194326 : (σ (M.op y y)) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq194231
  have eq194450 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq191464
       have i₂ := eq194326
       grind)
    | exact superpose eq194326 eq191464
    | exact resolve eq191464 eq194326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191464 eq194326
  have eq194552 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq194450
  have eq194980 : (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq190378
       have i₂ := eq194552
       grind)
    | exact superpose eq194552 eq190378
    | exact resolve eq190378 eq194552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190378 eq194552
  have eq195084 : (σ (M.op x x)) = (σ (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq194980
  have eq196349 : (M.op y y) = (τ (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq195084
       grind)
    | exact superpose eq195084 eq10
    | exact resolve eq10 eq195084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195084
  have eq196612 : (M.op x x) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq196349
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq196349
    | exact resolve eq196349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196349
  have eq196962 : (M.op x x) = (M.op (M.op x x) y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 y y
       have i₂ := eq196612
       grind)
    | exact superpose eq196612 eq20
    | exact resolve eq20 eq196612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196612
  have eq198155 : (M.op y x) = (M.op (M.op x x) x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq9 y x x
       have i₂ := eq196962
       grind)
    | exact superpose eq196962 eq9
    | exact resolve eq9 eq196962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198272 : (M.op x x) = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq198155
       have i₂ := eq20 x x
       grind)
    | exact superpose eq20 eq198155
    | exact resolve eq198155 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198155
  have eq199430 : (M.op x y) = (M.op (M.op x x) y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq20 y x
       have i₂ := eq198272
       grind)
    | exact superpose eq198272 eq20
    | exact resolve eq20 eq198272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq198272
  have eq199504 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq196962
       have i₂ := eq199430
       grind)
    | exact superpose eq199430 eq196962
    | exact resolve eq196962 eq199430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196962 eq199430
  have eq199585 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq199504
  have eq199889 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq190381
       have i₂ := eq199585
       grind)
    | exact superpose eq199585 eq190381
    | exact resolve eq190381 eq199585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190381 eq199585
  have eq199947 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq199889
  have eq199948 : x = (M.op x x) := by grind
  clear eq199947
  have eq199960 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq199948
       grind)
    | exact superpose eq199948 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq199948
       grind)
    | exact resolve eq12 eq199948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199963 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq96 x X0
       have i₂ := eq199948
       grind)
    | exact superpose eq199948 eq96
    | (have j0 := eq96 x X0
       grind)
    | exact resolve eq96 eq199948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq199948
  have eq200184 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq199963 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199963
  have eq200185 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq199960 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199960
  have eq204158 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq200184 (σ X0)
       grind)
    | exact superpose eq200184 eq15
    | exact resolve eq15 eq200184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200184
  have eq204376 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq204158 X0
       have i₂ := eq200185 X0
       grind)
    | exact superpose eq200185 eq204158
    | exact resolve eq204158 eq200185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200185 eq204158
  have eq210713 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq204376 y
       grind)
    | exact superpose eq204376 eq16
    | (have r₁ := eq16
       have r₂ := eq204376 y
       grind)
    | exact resolve eq16 eq204376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204376
  have eq211112 : False := by grind
  exact eq211112

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq286 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq291 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq286 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq292 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq291 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291
  have eq297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq292
    | (have j0 := eq292 X0 X1
       grind)
    | exact resolve eq292 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq298 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq297 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq540 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq298 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq298
    | exact resolve eq298 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq298 x y
       grind)
    | exact superpose eq298 eq16
    | (have j1 := eq298 x y
       grind)
    | exact resolve eq16 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq563 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq540 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq540
    | (have j0 := eq540 X0 X1
       grind)
    | exact resolve eq540 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq540
  have eq565 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq563
    | exact resolve eq563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq624 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq565 (τ X0) X1
       grind)
    | exact superpose eq565 eq18
    | (have j1 := eq565 (τ X0) X1
       grind)
    | exact resolve eq18 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq565
  have eq870 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq624 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq624
    | exact resolve eq624 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq923 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq870 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq870
    | (have j0 := eq870 X0 X1
       grind)
    | exact resolve eq870 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870
  have eq1008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq548
       have i₂ := eq923 x y
       grind)
    | exact superpose eq923 eq548
    | (have j1 := eq923 (σ x) (σ y)
       grind)
    | (have r₁ := eq548
       have r₂ := eq923 x y
       grind)
    | exact resolve eq548 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1009 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1008
  have eq1012 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1009
  have eq1053 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq548
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq548
    | exact resolve eq548 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548 eq1012
  have eq1054 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1053
  have eq1055 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1054
  have eq1062 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1055
  have eq1076 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1062
    | exact resolve eq1062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1118 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1076
       grind)
    | exact superpose eq1076 eq16
    | exact resolve eq16 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq1132 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1118
       have i₂ := eq923 x y
       grind)
    | exact superpose eq923 eq1118
    | (have j1 := eq923 x y
       grind)
    | (have r₁ := eq1118
       have r₂ := eq923 x y
       grind)
    | exact resolve eq1118 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923
  have eq1133 : x = (M.op y y) := by grind
  clear eq1132
  have eq1185 : (M.op x y) = (k x y) := by grind
  clear eq1133
  have eq1198 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1118
       have i₂ := eq1185
       grind)
    | exact superpose eq1185 eq1118
    | exact resolve eq1118 eq1185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118 eq1185
  have eq1201 : False := by grind
  exact eq1201

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_x_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq345 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq347 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq410 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
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
  clear eq347
  have eq443 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq410 X0 X2
       grind)
    | exact superpose eq410 eq9
    | (have j1 := eq410 X0 X2
       grind)
    | exact resolve eq9 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq641 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 X0 X0 x
       have i₂ := eq443 X0 x X2
       grind)
    | exact superpose eq443 eq9
    | (have j1 := eq443 X0 x X2
       grind)
    | exact resolve eq9 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq649 : ∀ X0 X2 : G, (k X2 X0) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have j0 := eq641 X0 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq641 x X2
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq641 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq665 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq649 (σ X0) (σ X1)
       grind)
    | exact superpose eq649 eq15
    | exact resolve eq15 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq692 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq649 X0 X1
       grind)
    | exact superpose eq649 eq665
    | exact resolve eq665 eq649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq665
  have eq996 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq692 x y
       grind)
    | exact superpose eq692 eq16
    | (have r₁ := eq16
       have r₂ := eq692 x y
       grind)
    | exact resolve eq16 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692
  have eq1012 : False := by grind
  exact eq1012

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_y_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 (M.op X2 X0)))) = X0 := by
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
  have eq28 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq16 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16
    | (have j0 := eq16 x
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq37 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op (M.op X1 (M.op X2 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 (M.op X2 X0)) X0 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq70 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq72 : y ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (k y x) := by
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
  have eq73 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq70
       grind)
    | exact superpose eq70 eq16
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq90
    | (have j0 := eq90 (σ X0) (σ X1)
       grind)
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq90
    | (have j0 := eq90 (σ y) (σ X0)
       grind)
    | exact resolve eq90 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq90 y x
       grind)
    | exact superpose eq90 eq69
    | (have j1 := eq90 y x
       grind)
    | exact resolve eq69 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
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
  have eq119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq116 eq90
    | (have j0 := eq90 (σ y) (σ x)
       grind)
    | exact resolve eq90 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq119
    | exact resolve eq119 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq123 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq120
       have r₂ := eq27
       grind)
    | exact resolve eq120 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq123
    | exact resolve eq123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq135 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq90 sF1 (σ X0)
       grind)
    | exact superpose eq90 eq37
    | (have j1 := eq90 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq125 eq51
    | exact resolve eq51 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq224 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq219 eq14
    | exact resolve eq14 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq229 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq224 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq224
       grind)
    | exact resolve eq13 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq229 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq266 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq231 eq84
    | exact resolve eq84 eq231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq231
  have eq315 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq224 eq266
    | exact resolve eq266 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq266
  have eq319 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq315
  have eq321 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq319
    | exact resolve eq319 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq319
  have eq324 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq90 y y
       have i₂ := eq321
       grind)
    | exact superpose eq321 eq90
    | (have j0 := eq90 y y
       grind)
    | exact resolve eq90 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq325 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq324
  have eq328 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq125 eq73
    | (have r₁ := eq73
       have r₂ := eq125
       grind)
    | exact resolve eq73 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq125
  have eq329 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq328
  have eq331 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 y
       have i₂ := eq325
       grind)
    | exact superpose eq325 eq14
    | exact resolve eq14 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq373 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq94 X0 X0
       grind)
    | exact superpose eq94 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq94 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq94 X0 X0
       grind)
    | exact resolve eq13 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq378 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq373 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq373 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq373 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373
  have eq458 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X0) (M.op X0 (M.op X2 (M.op X3 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X0 (M.op X1 (M.op X2 X0))) X1 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq483 : y = (M.op y (M.op y (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq331 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq331
    | (have j0 := eq331 x
       grind)
    | exact resolve eq331 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq494 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq483 eq14
    | exact resolve eq14 eq483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq728 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq329 eq116
    | exact resolve eq116 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq731 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq728
  have eq739 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq731 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq731
       grind)
    | exact resolve eq13 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq744 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq739 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq744 eq116
    | exact resolve eq116 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq744
  have eq762 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq759
  have eq767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq762
    | exact resolve eq762 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq769 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq767
       have r₂ := eq27
       grind)
    | exact resolve eq767 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq771 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq769 eq26
    | exact resolve eq26 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 : G, (σ (k x X0)) = (k (σ (M.op x y)) (σ X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq769 eq35
    | exact resolve eq35 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq779 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq769 eq116
    | exact resolve eq116 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq769
  have eq787 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq779
  have eq794 : ∀ X0 : G, (σ (k x X0)) = (σ (k (M.op x y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq37 eq773
    | exact resolve eq773 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq773
  have eq1992 : ∀ X0 : G, (σ y) ≠ (σ (k y X0)) ∨ (σ y) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have j0 := eq96 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq2159 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k (M.op x y) X0)) ∨ (σ (M.op x y)) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq138 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq2550 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ (M.op x y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq794 eq38
    | exact resolve eq38 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2555 : ∀ X0 : G, (k (M.op x y) X0) = (τ (σ (k x X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq794 eq16
    | exact resolve eq16 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq2598 : ∀ X0 : G, (k x X0) = (k (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2555 X0
       have i₂ := eq16 (k x X0)
       grind)
    | exact superpose eq16 eq2555
    | exact resolve eq2555 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555
  have eq2603 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ (M.op x y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq2550
    | (have j0 := eq2550 X0
       grind)
    | exact resolve eq2550 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq2621 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (k (σ x) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2603 X0
       have i₂ := eq38 X0 x
       grind)
    | exact superpose eq38 eq2603
    | exact resolve eq2603 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq2603
  have eq2626 : ∀ X0 : G, (k (σ x) X0) = (k (σ (M.op x y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2621 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2621
    | (have j0 := eq2621 X0
       grind)
    | exact resolve eq2621 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2621
  have eq3354 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq376 x y
       have i₂ := eq69
       grind)
    | exact superpose eq69 eq376
    | (have j0 := eq376 x y
       grind)
    | exact resolve eq376 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq3373 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3354
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3354
    | exact resolve eq3354 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3354
  have eq3428 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3373
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3373
    | exact resolve eq3373 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3373
  have eq3472 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3428
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3428
    | exact resolve eq3428 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428
  have eq3504 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3472
    | exact resolve eq3472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3472
  have eq4209 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq378 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq378
    | (have j0 := eq378 (τ X0) X1
       grind)
    | exact resolve eq378 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq378
  have eq4223 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4209 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4209
    | (have j0 := eq4209 X0 X1
       grind)
    | exact resolve eq4209 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4209
  have eq4245 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4223 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4223
    | (have j0 := eq4223 X0 X1
       grind)
    | exact resolve eq4223 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4223
  have eq4463 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op X0 (M.op X1 y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq458 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq458
    | (have j0 := eq458 y x X0 X1
       grind)
    | exact resolve eq458 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq40448 : (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq494 eq4463
    | exact resolve eq4463 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq67826 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40448 eq14
    | exact resolve eq14 eq40448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40448
  have eq67924 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq67826 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq67826
       grind)
    | exact resolve eq13 eq67826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67954 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq67924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67924
  have eq68449 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq67954 eq45
    | exact resolve eq45 eq67954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq68531 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq67954 eq2598
    | exact resolve eq2598 eq67954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq68587 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq68531
  have eq69237 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq68587 eq67954
    | exact resolve eq67954 eq68587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67954 eq68587
  have eq69249 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq69237
  have eq73518 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq69249 eq67826
    | exact resolve eq67826 eq69249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67826 eq69249
  have eq73562 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq73518
  have eq76000 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73562 eq68449
    | exact resolve eq68449 eq73562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68449 eq73562
  have eq76091 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq76000
  have eq76095 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq76091
    | exact resolve eq76091 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76091
  have eq76117 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76095 eq2626
    | exact resolve eq2626 eq76095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626 eq76095
  have eq76126 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq76117
  have eq76603 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76126 eq4245
    | (have j0 := eq4245 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq4245 (σ (M.op x y)) x
       have r₂ := eq76126
       grind)
    | exact resolve eq4245 eq76126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76126
  have eq76617 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq76603 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76603
  have eq84411 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq76617 eq787
    | exact resolve eq787 eq76617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq76617
  have eq84544 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq84411
  have eq84597 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq84544 eq771
    | exact resolve eq771 eq84544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771 eq84544
  have eq84644 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq84597
  have eq84646 : y = (M.op x y) := by
    first
    | (have r₁ := eq84644
       have r₂ := eq27
       grind)
    | exact resolve eq84644 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84644
  have eq85074 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq84646 eq20
    | exact resolve eq20 eq84646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85080 : y ≠ y ∨ x = (M.op x x) ∨ x = (k y x) := by
    first
    | exact superpose eq84646 eq72
    | (have r₁ := eq72
       have r₂ := eq84646
       grind)
    | exact resolve eq72 eq84646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq85192 : ∀ X0 X1 : G, y = (M.op y (M.op y (M.op y (M.op X0 (M.op X1 y))))) := by
    intro X0 X1
    first
    | exact superpose eq84646 eq4463
    | exact resolve eq4463 eq84646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4463
  have eq85260 : x = (k y x) ∨ x = (M.op x x) := by grind
  clear eq85080
  have eq85261 : y = (M.op y y) := by
    first
    | (have i₁ := eq85192 x x
       have i₂ := eq14 y x x
       grind)
    | exact superpose eq14 eq85192
    | exact resolve eq85192 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85192
  have eq85343 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq85074
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85074
    | exact resolve eq85074 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85074
  have eq85346 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq85343 eq26
    | exact resolve eq26 eq85343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq85417 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq85343 eq3504
    | exact resolve eq3504 eq85343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504
  have eq85562 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq85417
       have r₂ := eq27
       grind)
    | exact resolve eq85417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85417
  have eq85622 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq85261
       grind)
    | exact superpose eq85261 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq85261
       grind)
    | exact resolve eq13 eq85261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85652 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq85622 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85622
  have eq86408 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1992 y
       have i₂ := eq85652 y
       grind)
    | exact superpose eq85652 eq1992
    | (have j0 := eq1992 y
       grind)
    | exact resolve eq1992 eq85652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992 eq85652
  have eq86551 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq86408
       have i₂ := eq85261
       grind)
    | exact superpose eq85261 eq86408
    | exact resolve eq86408 eq85261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85261 eq86408
  have eq86674 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq86551
       have r₂ := eq24
       grind)
    | exact resolve eq86551 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86551
  have eq86750 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq85343 eq86674
    | exact resolve eq86674 eq85343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86674
  have eq86805 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq86750
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq86750
    | exact resolve eq86750 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq86750
  have eq86836 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq85343 eq86805
    | exact resolve eq86805 eq85343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86805
  have eq86932 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y))))) := by
    intro X0
    first
    | exact superpose eq86836 eq14
    | exact resolve eq14 eq86836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86836
  have eq94701 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq85346 eq86932
    | exact resolve eq86932 eq85346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86932
  have eq94795 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq94701 eq14
    | exact resolve eq14 eq94701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94701
  have eq100456 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq85260
       grind)
    | exact superpose eq85260 eq69
    | exact resolve eq69 eq85260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq85260
  have eq100508 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq85343 eq100456
    | exact resolve eq100456 eq85343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85343 eq100456
  have eq100532 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq100508
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq100508
    | exact resolve eq100508 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100508
  have eq101386 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq100532 eq90
    | (have j0 := eq90 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq90 eq100532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq100532
  have eq101395 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq85346 eq101386
    | exact resolve eq101386 eq85346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101386
  have eq101410 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq85346 eq101395
    | exact resolve eq101395 eq85346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101395
  have eq101419 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq101410
       have r₂ := eq27
       grind)
    | exact resolve eq101410 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101410
  have eq101426 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq101419
       grind)
    | exact superpose eq101419 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq101419
       grind)
    | exact resolve eq13 eq101419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101419
  have eq101456 : ∀ X0 : G, (k X0 x) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq101426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101426
  have eq102821 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq135
       have i₂ := eq101456 sF0
       grind)
    | exact superpose eq101456 eq135
    | exact resolve eq135 eq101456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq101456
  have eq103027 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq84646 eq102821
    | exact resolve eq102821 eq84646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102821
  have eq103130 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq103027
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103027
    | exact resolve eq103027 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103027
  have eq103203 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq103130
    | exact resolve eq103130 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103130
  have eq103266 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq103203
       have r₂ := eq85562
       grind)
    | exact resolve eq103203 eq85562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85562 eq103203
  have eq104166 : (σ x) = (M.op (σ x) (M.op (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq103266 eq94795
    | exact resolve eq94795 eq103266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94795
  have eq104167 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq85346 eq104166
    | exact resolve eq104166 eq85346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104166
  have eq104182 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq103266 eq104167
    | exact resolve eq104167 eq103266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103266 eq104167
  have eq104207 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq104182 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq104182
       grind)
    | exact resolve eq13 eq104182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104237 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq104207 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104207
  have eq104394 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq104237 eq49
    | exact resolve eq49 eq104237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq104237
  have eq104583 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq104182 eq104394
    | exact resolve eq104394 eq104182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104182 eq104394
  have eq104645 : x = (k x x) := by
    first
    | exact superpose eq28 eq104583
    | exact resolve eq104583 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq104583
  have eq104744 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq4245 x X0
       have i₂ := eq104645
       grind)
    | exact superpose eq104645 eq4245
    | (have j0 := eq4245 x X0
       grind)
    | (have r₁ := eq4245 x x
       have r₂ := eq104645
       grind)
    | exact resolve eq4245 eq104645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4245 eq104645
  have eq104758 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq104744 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104744
  have eq105150 : (σ (M.op x y)) ≠ (σ (M.op x (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2159 x
       have i₂ := eq104758 sF0
       grind)
    | exact superpose eq104758 eq2159
    | (have j0 := eq2159 x
       grind)
    | exact resolve eq2159 eq104758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2159 eq104758
  have eq105299 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq84646 eq105150
    | exact resolve eq105150 eq84646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84646 eq105150
  have eq105446 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq105299
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq105299
    | exact resolve eq105299 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq105299
  have eq105564 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have r₁ := eq105446
       have r₂ := eq20
       grind)
    | exact resolve eq105446 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq105446
  have eq105665 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq105564
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq105564
    | exact resolve eq105564 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq105564
  have eq105749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq85346 eq105665
    | exact resolve eq105665 eq85346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85346 eq105665
  have eq105806 : False := by grind
  exact eq105806

/-- `Equation422`: `x = x ◇ (x ◇ (y ◇ (z ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pyx_y_pyx_Equation422 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law422 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law422.models_iff G M).mp hM
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
  have eq272 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq275 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq273 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq273 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq273 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq286 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq275 (σ X0)
       grind)
    | exact superpose eq275 eq15
    | exact resolve eq15 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq275 (τ X0)
       grind)
    | exact superpose eq275 eq31
    | exact resolve eq31 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq299 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq292 X0
       have i₂ := eq275 X0
       grind)
    | exact superpose eq275 eq292
    | exact resolve eq292 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq305 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq286 X0
       have i₂ := eq275 X0
       grind)
    | exact superpose eq275 eq286
    | exact resolve eq286 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275 eq286
  have eq351 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq353 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq305 X0
       grind)
    | exact superpose eq305 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq354 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq351 X0 X1
       have j1 := eq353 X0 X1
       grind)
    | (have r₁ := eq351 X0 X1
       have r₂ := eq353 X0 X1
       grind)
    | exact resolve eq351 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq351 eq353
  have eq368 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq14
    | (have j0 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq14 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq299 X0
       grind)
    | exact superpose eq299 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq371 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq368 X0 X1
       have j1 := eq370 X0 X1
       grind)
    | (have r₁ := eq368 X0 X1
       have r₂ := eq370 X0 X1
       grind)
    | exact resolve eq368 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368 eq370
  have eq429 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq354 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq354
    | exact resolve eq354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq460 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq429 (σ x) (σ y)
       grind)
    | exact superpose eq429 eq16
    | (have j1 := eq429 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq467 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq429 X0 X1
       grind)
    | exact superpose eq429 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq429 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq429 X0 X1
       grind)
    | exact resolve eq13 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X1 X0) = X0 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq467 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq480 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq475 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq475 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq475 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq482 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq460
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq460
    | exact resolve eq460 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq507 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq480 X0 (τ X1)
       grind)
    | exact superpose eq480 eq17
    | (have j1 := eq480 X0 (τ X1)
       grind)
    | exact resolve eq17 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq480 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq371 X0 X1
       grind)
    | exact superpose eq371 eq18
    | (have j1 := eq371 X0 X1
       grind)
    | exact resolve eq18 eq371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1852 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq507 (τ X0) X1
       grind)
    | exact superpose eq507 eq18
    | (have j1 := eq507 (τ X0) X1
       grind)
    | exact resolve eq18 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq507
  have eq1861 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1852 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1852
    | (have j0 := eq1852 X0 X1
       grind)
    | exact resolve eq1852 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852
  have eq1882 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1861 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1861
    | (have j0 := eq1861 X0 X1
       grind)
    | exact resolve eq1861 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq1887 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1882 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1882
    | (have j0 := eq1882 X0 X1
       grind)
    | exact resolve eq1882 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1882
  have eq1960 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1887 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1887
    | (have j0 := eq1887 X1 (σ X0)
       grind)
    | exact resolve eq1887 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887
  have eq2694 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1960 X0 X0
       have i₂ := eq480 X0 (σ X0)
       grind)
    | exact superpose eq480 eq1960
    | (have j0 := eq1960 X1 X0
       have j1 := eq480 X0 (σ X1)
       grind)
    | exact resolve eq1960 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq1960
  have eq2738 : ∀ X0 X1 : G, (k (σ X1) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2694 X0 X1
       have j1 := eq513 (σ X1) X0
       grind)
    | (have r₁ := eq2694 X1 X1
       have r₂ := eq513 (σ X1) X1
       grind)
    | exact resolve eq2694 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694
  have eq2814 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X0))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2738 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2738
    | exact resolve eq2738 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2845 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq2738 (σ X0) X1
       grind)
    | exact superpose eq2738 eq22
    | (have j1 := eq2738 (σ X0) X1
       grind)
    | exact resolve eq22 eq2738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738
  have eq2857 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2845 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2845
    | (have j0 := eq2845 X0 X1
       grind)
    | exact resolve eq2845 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq2875 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2857 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2857
    | (have j0 := eq2857 X0 X1
       grind)
    | exact resolve eq2857 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857
  have eq2884 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2875 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2875
    | (have j0 := eq2875 X0 X1
       grind)
    | exact resolve eq2875 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2875
  have eq2926 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X1))
       have i₂ := eq2814 X1 X0
       grind)
    | exact superpose eq2814 eq10
    | (have j1 := eq2814 X1 X0
       grind)
    | exact resolve eq10 eq2814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2814
  have eq3008 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2884 x y
       grind)
    | exact superpose eq2884 eq16
    | (have j1 := eq2884 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2884 x y
       grind)
    | exact resolve eq16 eq2884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884
  have eq3055 : x = (k y x) := by grind
  clear eq3008
  have eq3105 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (M.op (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2926 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2926
    | (have j0 := eq2926 X1 (σ X0)
       grind)
    | exact resolve eq2926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2926
  have eq4173 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (τ (M.op (σ X0) (σ X1))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq3105 X1 (σ X0)
       grind)
    | exact superpose eq3105 eq22
    | (have j1 := eq3105 X1 (σ X0)
       grind)
    | exact resolve eq22 eq3105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3105
  have eq4185 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (τ (M.op (σ X0) (σ X1))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4173 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4173
    | (have j0 := eq4173 X0 X1
       grind)
    | exact resolve eq4173 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4173
  have eq4205 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (τ (M.op (σ X0) (σ X1))) = (M.op (τ (σ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4185 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4185
    | (have j0 := eq4185 X0 X1
       grind)
    | exact resolve eq4185 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4185
  have eq4214 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4205 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4205
    | (have j0 := eq4205 X0 X1
       grind)
    | exact resolve eq4205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4205
  have eq4251 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X1) ∨ (k X1 X0) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4214 X0 X1
       have i₂ := eq429 (σ X0) (σ X1)
       grind)
    | exact superpose eq429 eq4214
    | (have j0 := eq4214 X0 X1
       have j1 := eq429 (σ X0) (σ X1)
       grind)
    | exact resolve eq4214 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429 eq4214
  have eq4307 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4251 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4251
    | (have j0 := eq4251 X0 X1
       grind)
    | exact resolve eq4251 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4251
  have eq4313 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4307 X0 X1
       have j1 := eq513 X1 X0
       grind)
    | (have r₁ := eq4307 X1 X0
       have r₂ := eq513 X0 X1
       grind)
    | exact resolve eq4307 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq4307
  have eq4317 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4313 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4313
    | (have j0 := eq4313 X0 X1
       grind)
    | exact resolve eq4313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4313
  have eq4336 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (k (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4317 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4317
    | (have j0 := eq4317 X1 (τ X0)
       grind)
    | exact resolve eq4317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4317
  have eq4453 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4336 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq4336
    | (have j0 := eq4336 X0 X1
       grind)
    | exact resolve eq4336 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq4336
  have eq4530 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq371 X0 (τ X1)
       have i₂ := eq4453 X1 (τ X0)
       grind)
    | exact superpose eq4453 eq371
    | (have j0 := eq371 X0 (τ X1)
       have j1 := eq4453 X1 (τ X0)
       grind)
    | exact resolve eq371 eq4453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq4453
  have eq4534 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X1)) ∨ (k X1 (σ (τ X0))) = (M.op (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq4530 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4530
  have eq4541 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4534 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4534
    | (have j0 := eq4534 X0 X1
       grind)
    | exact resolve eq4534 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4534
  have eq4639 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4541 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4541
    | (have j0 := eq4541 (σ X0) X1
       grind)
    | exact resolve eq4541 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4541
  have eq4724 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4639 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4639
    | (have j0 := eq4639 X1 (σ X0)
       grind)
    | exact resolve eq4639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4639
  have eq4828 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4724 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4724
    | (have j0 := eq4724 X0 X1
       grind)
    | exact resolve eq4724 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724
  have eq4897 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4828 y x
       grind)
    | exact superpose eq4828 eq16
    | (have j1 := eq4828 y x
       grind)
    | exact resolve eq16 eq4828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828
  have eq4989 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4897
       have i₂ := eq3055
       grind)
    | exact superpose eq3055 eq4897
    | exact resolve eq4897 eq3055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4897
  have eq7946 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1130 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1130
    | exact resolve eq1130 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq8074 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7946 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq7946
    | (have j0 := eq7946 X0 X1
       grind)
    | exact resolve eq7946 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7946
  have eq8135 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8074 x y
       have i₂ := eq3055
       grind)
    | exact superpose eq3055 eq8074
    | (have j0 := eq8074 x y
       grind)
    | exact resolve eq8074 eq3055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8074
  have eq8223 : x = (M.op x y) := by
    first
    | (have r₁ := eq8135
       have r₂ := eq4989
       grind)
    | exact resolve eq8135 eq4989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4989 eq8135
  have eq8227 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq482
       have i₂ := eq8223
       grind)
    | exact superpose eq8223 eq482
    | exact resolve eq482 eq8223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq8248 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq8227
  have eq8249 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8248
       have i₂ := eq3055
       grind)
    | exact superpose eq3055 eq8248
    | exact resolve eq8248 eq3055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055 eq8248
  have eq8253 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8249
       grind)
    | exact superpose eq8249 eq16
    | exact resolve eq16 eq8249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8249
  have eq8289 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq8253
       have i₂ := eq8223
       grind)
    | exact superpose eq8223 eq8253
    | exact resolve eq8253 eq8223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8223 eq8253
  have eq8290 : False := by grind
  exact eq8290

/-- `Equation426`: `x = x ◇ (y ◇ (x ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_y_pxy_Equation426 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law426 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law426.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq269 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq273 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq375 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq273 (σ y) (σ x)
       grind)
    | exact superpose eq273 eq16
    | (have j1 := eq273 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq273 X0 X1
       grind)
    | exact superpose eq273 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq273 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq273 X0 X1
       grind)
    | exact resolve eq13 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq386 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq385 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq385 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq385 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq389 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq375
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq375
    | exact resolve eq375 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq414 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq386 X1 (τ X0)
       grind)
    | exact superpose eq386 eq17
    | (have j1 := eq386 X1 (τ X0)
       grind)
    | exact resolve eq17 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq420 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq386 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq414 X1 (τ X0)
       grind)
    | exact superpose eq414 eq18
    | (have j1 := eq414 X1 (τ X0)
       grind)
    | exact resolve eq18 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq414
  have eq578 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq573
    | (have j0 := eq573 X0 X1
       grind)
    | exact resolve eq573 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq592 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq578
    | (have j0 := eq578 X0 X1
       grind)
    | exact resolve eq578 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq595 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq592 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq592
    | (have j0 := eq592 X0 X1
       grind)
    | exact resolve eq592 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq650 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq595 X0 X1
       have i₂ := eq386 X0 X1
       grind)
    | exact superpose eq386 eq595
    | (have j0 := eq595 X1 X0
       have j1 := eq386 X1 X0
       grind)
    | exact resolve eq595 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386 eq595
  have eq707 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq650 X0 X1
       have j1 := eq420 X0 X1
       grind)
    | (have r₁ := eq650 X0 X1
       have r₂ := eq420 X0 X1
       grind)
    | exact resolve eq650 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420 eq650
  have eq772 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq707 X1 (σ X0)
       grind)
    | exact superpose eq707 eq22
    | (have j1 := eq707 X1 (σ X0)
       grind)
    | exact resolve eq22 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq707
  have eq806 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq772 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq772
    | (have j0 := eq772 X0 X1
       grind)
    | exact resolve eq772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq825 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq806 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq806
    | (have j0 := eq806 X0 X1
       grind)
    | exact resolve eq806 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq1050 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq825 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq825
    | exact resolve eq825 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1112 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1050 x y
       grind)
    | exact superpose eq1050 eq16
    | (have j1 := eq1050 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1050 x y
       grind)
    | exact resolve eq16 eq1050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1125 : y = (k x y) := by grind
  clear eq1112
  have eq1228 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq389
       have i₂ := eq273 y x
       grind)
    | exact superpose eq273 eq389
    | (have j1 := eq273 y x
       grind)
    | exact resolve eq389 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1230 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1228
  have eq1231 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1230
       have i₂ := eq1125
       grind)
    | exact superpose eq1125 eq1230
    | exact resolve eq1230 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1232 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1231
       have i₂ := eq1125
       grind)
    | exact superpose eq1125 eq1231
    | exact resolve eq1231 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231
  have eq1234 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq389
       have i₂ := eq1232
       grind)
    | exact superpose eq1232 eq389
    | exact resolve eq389 eq1232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq1232
  have eq1243 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1234
  have eq1244 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1243
       have i₂ := eq1125
       grind)
    | exact superpose eq1125 eq1243
    | exact resolve eq1243 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1245 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1244
  have eq1249 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1245
       grind)
    | exact superpose eq1245 eq16
    | exact resolve eq16 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq1266 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1249
       have i₂ := eq273 y x
       grind)
    | exact superpose eq273 eq1249
    | (have j1 := eq273 y x
       grind)
    | exact resolve eq1249 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq1268 : (M.op x y) = (k x y) := by grind
  clear eq1266
  have eq1270 : y = (M.op x y) := by
    first
    | (have i₁ := eq1268
       have i₂ := eq1125
       grind)
    | exact superpose eq1125 eq1268
    | exact resolve eq1268 eq1125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1125 eq1268
  have eq1272 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1249
       have i₂ := eq1270
       grind)
    | exact superpose eq1270 eq1249
    | exact resolve eq1249 eq1270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249 eq1270
  have eq1283 : False := by grind
  exact eq1283
