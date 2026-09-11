import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2663`: `x = ((x ◇ y) ◇ (x ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(X,Y) then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pxy_pxy_x_pxy_Equation2663 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2663 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2663.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op a b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = X0 := by
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
  clear eq24 eq35
  have eq50 : x = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) ≠ X0 ∨ (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
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
  have eq69 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq68
       have i₂ := eq65 sF2
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq68
  have eq78 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by
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
  have eq79 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
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
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq87 x y
       grind)
    | exact superpose eq87 eq44
    | (have j1 := eq87 x y
       grind)
    | exact resolve eq44 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq114
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114
    | exact resolve eq114 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq830 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq115 eq87
    | (have j0 := eq87 (σ x) (σ y)
       grind)
    | exact resolve eq87 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq830
    | exact resolve eq830 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830
  have eq834 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq831
       have r₂ := eq27
       grind)
    | exact resolve eq831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq836 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq834
    | exact resolve eq834 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq838 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq836 eq79
    | (have r₁ := eq79
       have r₂ := eq836
       grind)
    | exact resolve eq79 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq836
  have eq850 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq838
  have eq875 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) ≠ X0 ∨ (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq59
    | (have j0 := eq59 X0 X1
       grind)
    | exact resolve eq59 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq876 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) ≠ X0 ∨ (k (M.op (M.op X0 X0) X1) X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq875 X0 X1
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq875
    | (have j0 := eq875 X0 X1
       grind)
    | exact resolve eq875 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq875
  have eq921 : (M.op x y) ≠ (M.op y x) ∨ (M.op x y) = (k x y) := by
    first
    | exact superpose eq50 eq876
    | exact resolve eq876 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq51 eq876
    | exact resolve eq876 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq1756 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq850 eq923
    | (have r₁ := eq923
       have r₂ := eq850
       grind)
    | exact resolve eq923 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq923
  have eq1761 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq1756
  have eq2147 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq115 eq1761
    | exact resolve eq1761 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1761 eq115
    | exact resolve eq115 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1761
  have eq2153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq2149
  have eq2154 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq2147
  have eq2155 : (σ x) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq2153
       have r₂ := eq27
       grind)
    | exact resolve eq2153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq2156 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq2154
       have r₂ := eq27
       grind)
    | exact resolve eq2154 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154
  have eq2160 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq69
       have i₂ := eq2156
       grind)
    | exact superpose eq2156 eq69
    | exact resolve eq69 eq2156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2156
  have eq2175 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq2160
    | exact resolve eq2160 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2160
  have eq2421 : (τ (σ x)) = (k x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2155 eq58
    | exact resolve eq58 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq2155
  have eq2427 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq28 eq2421
    | exact resolve eq2421 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2421
  have eq2617 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq2427
       grind)
    | exact superpose eq2427 eq78
    | (have r₁ := eq78
       have r₂ := eq2427
       grind)
    | exact resolve eq78 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2619 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq2427
       grind)
    | exact superpose eq2427 eq69
    | exact resolve eq69 eq2427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427
  have eq2631 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq2617
  have eq2632 : (M.op x y) = (M.op y x) ∨ x = (k x y) := by grind
  clear eq2631
  have eq2635 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq2619
    | exact resolve eq2619 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq3432 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq921
       have i₂ := eq2632
       grind)
    | exact superpose eq2632 eq921
    | (have r₁ := eq921
       have r₂ := eq2632
       grind)
    | exact resolve eq921 eq2632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921 eq2632
  have eq3439 : (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq3432
  have eq3584 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq3439
       grind)
    | exact superpose eq3439 eq44
    | exact resolve eq44 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439
  have eq3587 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | exact superpose eq20 eq3584
    | exact resolve eq3584 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3584
  have eq3991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq3587 eq87
    | (have j0 := eq87 (σ x) (σ y)
       grind)
    | exact resolve eq87 eq3587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587
  have eq3992 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq3991
    | exact resolve eq3991 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991
  have eq3995 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | (have r₁ := eq3992
       have r₂ := eq27
       grind)
    | exact resolve eq3992 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq3997 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq3995
    | exact resolve eq3995 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3995
  have eq4016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq3997 eq2635
    | exact resolve eq2635 eq3997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2635 eq3997
  have eq4035 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq4016
  have eq4040 : x = (k x y) := by
    first
    | (have r₁ := eq4035
       have r₂ := eq27
       grind)
    | exact resolve eq4035 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035
  have eq4046 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq4040
       grind)
    | exact superpose eq4040 eq44
    | exact resolve eq44 eq4040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq4047 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq87 x y
       have i₂ := eq4040
       grind)
    | exact superpose eq4040 eq87
    | (have j0 := eq87 x y
       grind)
    | exact resolve eq87 eq4040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4040
  have eq4048 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq4047
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4047
    | exact resolve eq4047 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4047
  have eq4049 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq4046
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4046
    | exact resolve eq4046 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4046
  have eq4051 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4048
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4048
    | exact resolve eq4048 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4048
  have eq4060 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4049 eq87
    | (have j0 := eq87 (σ x) (σ y)
       grind)
    | exact resolve eq87 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq4049
  have eq4061 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq4060
    | exact resolve eq4060 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4060
  have eq4064 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4061
    | exact resolve eq4061 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4061
  have eq4068 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq69
       have i₂ := eq4051
       grind)
    | exact superpose eq4051 eq69
    | exact resolve eq69 eq4051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4051
  have eq4090 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4068
    | exact resolve eq4068 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4068
  have eq4105 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4064 eq2175
    | exact resolve eq2175 eq4064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4128 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4105
       have r₂ := eq27
       grind)
    | exact resolve eq4105 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4105
  have eq4131 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4128 eq51
    | exact resolve eq51 eq4128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4186 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq54 eq4131
    | exact resolve eq4131 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq4131
  have eq4321 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4090 eq4064
    | exact resolve eq4064 eq4090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4341 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4321
       have r₂ := eq27
       grind)
    | exact resolve eq4321 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321
  have eq4344 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4341 eq27
    | exact resolve eq27 eq4341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4341
  have eq4605 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4128 eq4186
    | exact resolve eq4186 eq4128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4128 eq4186
  have eq4643 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4605
  have eq4838 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4643 eq2175
    | exact resolve eq2175 eq4643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq4843 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4643 eq4090
    | exact resolve eq4090 eq4643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4090 eq4643
  have eq4859 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq4843
  have eq4863 : (σ (M.op x y)) = (σ x) := by grind
  clear eq4838
  have eq4872 : x = (M.op x y) := by
    first
    | (have r₁ := eq4859
       have r₂ := eq4344
       grind)
    | exact resolve eq4859 eq4344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4344 eq4859
  have eq5021 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4863 eq4064
    | exact resolve eq4064 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4064
  have eq5028 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq5021
       have r₂ := eq27
       grind)
    | exact resolve eq5021 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5021
  have eq5042 : x = (M.op (M.op x x) y) := by
    first
    | exact superpose eq4872 eq50
    | exact resolve eq50 eq4872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq5080 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5042
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq5042
    | exact resolve eq5042 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq5042
  have eq5085 : x = (M.op x x) := by
    first
    | exact superpose eq4872 eq5080
    | exact resolve eq5080 eq4872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4872 eq5080
  have eq5318 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq69
       have i₂ := eq5085
       grind)
    | exact superpose eq5085 eq69
    | exact resolve eq69 eq5085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq5085
  have eq5345 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq4863 eq5318
    | exact resolve eq5318 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5318
  have eq5349 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5028 eq5345
    | exact resolve eq5345 eq5028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5028 eq5345
  have eq5351 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5349
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5349
    | exact resolve eq5349 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5349
  have eq5353 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4863 eq5351
    | exact resolve eq5351 eq4863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4863 eq5351
  have eq5354 : False := by grind
  exact eq5354

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_x_pxx_pxy_pyx_Equation2685 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
    intro X0 X1 X2
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
  have eq52 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 y)) X0) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 x y X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op x y)) x) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 y x
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ y) (σ x)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ x) (σ y) X0
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq30
  have eq80 : x = (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op y y))) := by
    first
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq115 (σ X0)
       grind)
    | exact superpose eq115 eq15
    | exact resolve eq15 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq135 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq135
    | exact resolve eq135 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq135
  have eq194 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
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
  have eq237 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq194 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq194
    | exact resolve eq194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq363 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq60
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq367 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq363
    | exact resolve eq363 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq369 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq367
    | exact resolve eq367 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq371 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq369
    | exact resolve eq369 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq381 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X5 (M.op X0 X4))) X5) = (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X3 (M.op X2 X4) (M.op X0 X4) X5
       have i₂ := eq53 X0 X4 X2 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq391 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) (M.op y y)) X1)) = (M.op (M.op X0 x) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq80 eq53
    | exact resolve eq53 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 X3) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X1 X2 x
       have i₂ := eq53 X0 X3 X2 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 x X2
       have i₂ := eq53 X0 x X2 X1
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x
       have i₂ := eq53 sF0 x y x
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq57 x
       have i₂ := eq53 sF4 x sF3 x
       grind)
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq53 (M.op X0 X1) X2 X1 x
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op (M.op X0 X1) (M.op X2 X1))) (M.op X0 (M.op X4 X2))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X3 X4 (M.op X0 (M.op X4 X2))
       have i₂ := eq53 X0 X1 X2 X4
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x y) (M.op (M.op X0 X1) (M.op X2 X1))) (M.op X0 (M.op y X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 (M.op y X2))
       have i₂ := eq53 X0 X1 X2 y
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X1) (M.op X2 X1))) (M.op X0 (M.op (σ y) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op X0 (M.op sF3 X2))
       have i₂ := eq53 X0 X1 X2 sF3
       grind)
    | exact superpose eq53 eq57
    | exact resolve eq57 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq487 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op x y)) x) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq414 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq414
    | (have j0 := eq414 X0 x y
       grind)
    | exact resolve eq414 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq414
    | (have j0 := eq414 X0 (σ x) (σ y)
       grind)
    | exact resolve eq414 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq512 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq414 (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X1) X2 X3
       have i₂ := eq414 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq414 eq414
    | exact resolve eq414 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op X0 X1) y)) = (M.op (M.op x X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq52 eq414
    | exact resolve eq414 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq529 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X1 (M.op X2 X1))) X1 X2
       have i₂ := eq414 X0 X1 (M.op X2 X1)
       grind)
    | exact superpose eq414 eq9
    | exact resolve eq9 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op y (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq54 (M.op X0 (M.op y sF0))
       have i₂ := eq414 X0 y sF0
       grind)
    | exact superpose eq414 eq54
    | exact resolve eq54 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq56 (M.op X0 (M.op sF3 sF4))
       have i₂ := eq414 X0 sF3 sF4
       grind)
    | exact superpose eq414 eq56
    | exact resolve eq56 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 (M.op X1 y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X1 y)) X1)
       have i₂ := eq414 X0 X1 y
       grind)
    | exact superpose eq414 eq54
    | exact resolve eq54 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 (M.op X1 y)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op (M.op X0 (M.op X1 y)) X1)
       have i₂ := eq414 X0 X1 y
       grind)
    | exact superpose eq414 eq52
    | exact resolve eq52 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq541 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (M.op X1 (σ y))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op (M.op X0 (M.op X1 sF3)) X1)
       have i₂ := eq414 X0 X1 sF3
       grind)
    | exact superpose eq414 eq57
    | exact resolve eq57 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq542 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X0 (M.op X1 (σ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op (M.op X0 (M.op X1 sF3)) X1)
       have i₂ := eq414 X0 X1 sF3
       grind)
    | exact superpose eq414 eq56
    | exact resolve eq56 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x))) := by
    intro X0
    first
    | exact superpose eq542 eq541
    | (have j0 := eq541 X0 (σ x)
       grind)
    | exact resolve eq541 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq546 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 (M.op x y)) x)) := by
    intro X0
    first
    | (have i₁ := eq540 X0 x
       have i₂ := eq539 X0 x
       grind)
    | (have i₁ := eq540 X0 x
       have i₂ := eq539 X0 x
       grind)
    | exact superpose eq539 eq540
    | (have j0 := eq540 X0 x
       grind)
    | exact resolve eq540 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq558 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X2 X4)) (M.op (M.op X0 (M.op X1 X2)) X1)) = (M.op (M.op X3 X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq381 X0 X1 X2 X3 X4 x
       have i₂ := eq512 X3 x X0 X4
       grind)
    | exact superpose eq512 eq381
    | exact resolve eq381 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq567 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have i₁ := eq487 (M.op X0 (M.op sF0 x))
       have i₂ := eq414 X0 sF0 x
       grind)
    | exact superpose eq414 eq487
    | exact resolve eq487 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487
  have eq575 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) (M.op y y)) X1)) = (M.op (M.op X0 x) y) := by
    intro X0 X1
    first
    | exact superpose eq567 eq391
    | exact resolve eq391 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq589 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq508 (M.op X0 (M.op sF4 sF2))
       have i₂ := eq414 X0 sF4 sF2
       grind)
    | exact superpose eq414 eq508
    | exact resolve eq508 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) = (σ (M.op (M.op y (M.op x y)) x)) := by
    first
    | exact superpose eq530 eq136
    | exact resolve eq136 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq531 eq414
    | exact resolve eq414 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq828 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq424 (M.op X0 (M.op X3 X2)) X3 X4
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq424
    | exact resolve eq424 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq829 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) (M.op (M.op (M.op x y) (M.op y y)) X0)) := by
    intro X0
    first
    | exact superpose eq80 eq424
    | exact resolve eq424 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) (M.op y y)) X0) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq88 eq424
    | exact resolve eq424 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq842 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) X0) (M.op (σ x) X0)) := by
    intro X0
    first
    | exact superpose eq107 eq424
    | exact resolve eq424 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq914 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 (M.op X1 X2))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X4 X3)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3 X4
       have i₂ := eq424 X0 X1 X2
       grind)
    | exact superpose eq424 eq53
    | exact resolve eq53 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : (M.op (M.op x y) x) = (M.op (M.op x x) y) := by
    first
    | exact superpose eq575 eq829
    | exact resolve eq829 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq829
  have eq974 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4) (M.op (M.op X4 X5) (M.op X3 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq55 X4 (M.op X0 (M.op X3 X2)) X3 X5
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq995 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 (M.op X0 (M.op X1 X2)) X1 X3
       have i₂ := eq414 X0 X1 X2
       grind)
    | exact superpose eq414 eq55
    | exact resolve eq55 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq997 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X2 X3) (M.op X1 X3)) X4) (M.op X2 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X2 X3) (M.op X1 X3)) (M.op X0 X1) X2 X4
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000 : ∀ X0 : G, (M.op x y) = (M.op x (M.op (M.op (M.op (M.op x y) (M.op y y)) X0) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq80 eq55
    | exact resolve eq55 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1007 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) X0) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq101 eq55
    | exact resolve eq55 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq1087 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have i₂ := eq55 (M.op X1 X2) X0 X1 X2
       grind)
    | exact superpose eq55 eq9
    | exact resolve eq9 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X2 X3)) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq414 (M.op (M.op X0 X1) X2) (M.op X2 X3) (M.op X1 X3)
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq414
    | exact resolve eq414 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) (M.op (M.op X1 X4) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X2) X3 (M.op X1 X4) (M.op X2 X4)
       have i₂ := eq55 X2 X0 X1 X4
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1098 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) = (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X5 X4)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) X2) (M.op (M.op X2 X3) (M.op X1 X3)) X4 X5
       have i₂ := eq55 X2 X0 X1 X3
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X5 (M.op (M.op X0 X4) X2))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 X1 (M.op (M.op X2 X3) (M.op X4 X3)) (M.op (M.op X0 X4) X2) X5
       have i₂ := eq55 X2 X0 X4 X3
       grind)
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1104 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X4 X3))) X0) = (M.op (M.op X1 (M.op X0 X4)) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1099 X0 X1 X2 X3 X4 x
       have i₂ := eq512 X1 x (M.op X0 X4) X2
       grind)
    | exact superpose eq512 eq1099
    | exact resolve eq1099 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq1105 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op (M.op X2 X3) (M.op X1 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1098 X0 X1 X2 X3 X4 x
       have i₂ := eq914 X0 X1 X2 X4 x
       grind)
    | exact superpose eq914 eq1098
    | exact resolve eq1098 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq1098
  have eq1142 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq842 eq1007
    | exact resolve eq1007 eq842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842 eq1007
  have eq1145 : (M.op x y) = (M.op x (M.op x (M.op x y))) := by
    first
    | exact superpose eq834 eq1000
    | exact resolve eq1000 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq1000
  have eq1147 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op X2 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq997 X0 X1 X2 x x
       have i₂ := eq828 X2 x X1 X2 x
       grind)
    | exact superpose eq828 eq997
    | exact resolve eq997 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq997
  have eq1198 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1142 eq414
    | exact resolve eq414 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1222 : x = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq1145 eq414
    | exact resolve eq414 eq1145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1247 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
    first
    | exact superpose eq1198 eq508
    | exact resolve eq508 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq1254 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (M.op X1 (M.op (σ x) (σ y))))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1198 eq55
    | exact resolve eq55 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1259 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (σ y)) (M.op (σ x) (M.op X1 (M.op (σ x) (σ y))))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq589 eq1254
    | exact resolve eq1254 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq1254
  have eq1273 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (M.op x y) x)) (M.op x (M.op X1 (M.op x y)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1222 eq55
    | exact resolve eq55 eq1222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq1222
  have eq1278 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) y) (M.op x (M.op X1 (M.op x y)))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq567 eq1273
    | exact resolve eq1273 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq1273
  have eq1288 : ∀ X0 : G, (M.op (M.op (M.op X0 y) (M.op (M.op x y) x)) (M.op x x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 y (M.op x x)
       have i₂ := eq948
       grind)
    | exact superpose eq948 eq9
    | exact resolve eq9 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1291 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 (M.op (M.op x y) x)) (M.op x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 y (M.op x x)
       have i₂ := eq948
       grind)
    | exact superpose eq948 eq53
    | exact resolve eq53 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1295 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) x)) (M.op x x)) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq414 X0 (M.op x x) y
       have i₂ := eq948
       grind)
    | exact superpose eq948 eq414
    | exact resolve eq414 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1299 : ∀ X0 : G, (M.op (M.op (M.op X0 x) (M.op x y)) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1295 X0
       have i₂ := eq1089 X0 x sF0 x
       grind)
    | exact superpose eq1089 eq1295
    | exact resolve eq1295 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1295
  have eq1303 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1291 X0 X1
       have i₂ := eq1089 X0 x sF0 x
       grind)
    | exact superpose eq1089 eq1291
    | exact resolve eq1291 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1304 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1288 X0
       have i₂ := eq1089 (M.op X0 y) x sF0 x
       grind)
    | exact superpose eq1089 eq1288
    | exact resolve eq1288 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1288
  have eq1318 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1299 (M.op X0 (M.op x sF0))
       have i₂ := eq414 X0 x sF0
       grind)
    | exact superpose eq414 eq1299
    | exact resolve eq1299 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1321 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1299 eq54
    | exact resolve eq54 eq1299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1299
  have eq1337 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 y)) X1) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq1321 eq539
    | exact resolve eq539 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq1338 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1321 eq546
    | exact resolve eq546 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq1351 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x x) (M.op x y)) := by
    first
    | exact superpose eq1321 eq88
    | exact resolve eq88 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq1355 : (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) = (σ (M.op (M.op y x) (M.op x y))) := by
    first
    | exact superpose eq1321 eq611
    | exact resolve eq611 eq1321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq1321
  have eq1377 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op y x)) := by
    intro X0
    first
    | (have i₁ := eq1304 (M.op X0 (M.op y x))
       have i₂ := eq414 X0 y x
       grind)
    | exact superpose eq414 eq1304
    | exact resolve eq1304 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1414 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq1247 eq9
    | exact resolve eq9 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1421 : ∀ X0 : G, (M.op (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) (M.op (σ x) (σ x))) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1247 eq414
    | exact resolve eq414 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1247
  have eq1425 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1421 X0
       have i₂ := eq1089 X0 sF2 sF4 sF2
       grind)
    | exact superpose eq1089 eq1421
    | exact resolve eq1421 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421
  have eq1430 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1414 X0
       have i₂ := eq1089 (M.op X0 sF3) sF2 sF4 sF2
       grind)
    | exact superpose eq1089 eq1414
    | exact resolve eq1414 eq1089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089 eq1414
  have eq1618 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
    first
    | (have i₁ := eq136 (M.op y x)
       have i₂ := eq1377 (M.op y x)
       grind)
    | exact superpose eq1377 eq136
    | exact resolve eq136 eq1377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1638 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (M.op y x) X1)) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X1 (M.op y x)
       have i₂ := eq1377 (M.op X0 (M.op (M.op y x) X1))
       grind)
    | exact superpose eq1377 eq53
    | exact resolve eq53 eq1377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1377
  have eq1667 : (M.op (σ (M.op y (M.op x y))) (σ (M.op y (M.op x y)))) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
    first
    | exact superpose eq1355 eq1618
    | exact resolve eq1618 eq1355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618
  have eq1679 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
    first
    | exact superpose eq1667 eq1355
    | exact resolve eq1355 eq1667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355 eq1667
  have eq1697 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1425 (M.op X0 (M.op sF2 sF4))
       have i₂ := eq414 X0 sF2 sF4
       grind)
    | exact superpose eq414 eq1425
    | exact resolve eq1425 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1700 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1425 eq56
    | exact resolve eq56 eq1425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1425
  have eq1716 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1700 eq542
    | exact resolve eq542 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq542
  have eq1717 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1700 eq544
    | exact resolve eq544 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq1700
  have eq1759 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq1430 (M.op X0 (M.op sF3 sF2))
       have i₂ := eq414 X0 sF3 sF2
       grind)
    | exact superpose eq414 eq1430
    | exact resolve eq1430 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq2030 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (M.op (σ y) (σ x)) X1)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1759 eq53
    | exact resolve eq53 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq2092 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op X0 (M.op x (M.op y X1))) := by
    intro X0 X1
    first
    | exact superpose eq422 eq1087
    | exact resolve eq1087 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2093 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) = (M.op X0 (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq423 eq1087
    | exact resolve eq1087 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2096 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X0 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1087 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
       have i₂ := eq424 X0 X2 X3
       grind)
    | exact superpose eq424 eq1087
    | exact resolve eq1087 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2098 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) (M.op X3 X2))) = (M.op X1 (M.op X0 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1087 X1 (M.op (M.op X0 X2) (M.op X3 X2)) X3
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq1087
    | exact resolve eq1087 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2112 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1087 X1 (M.op X0 (M.op X2 X2)) X2
       have i₂ := eq414 X0 X2 X2
       grind)
    | exact superpose eq414 eq1087
    | exact resolve eq1087 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2148 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op X2 X1)
       have i₂ := eq1087 (M.op X0 X1) X2 X1
       grind)
    | exact superpose eq1087 eq9
    | exact resolve eq9 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq2232 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq995 X0 X1 X2 x
       have i₂ := eq2098 X2 X0 x X1
       grind)
    | exact superpose eq2098 eq995
    | exact resolve eq995 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq2236 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X1 (M.op X0 X4)) X2) = (M.op (M.op X1 (M.op X2 X4)) X0) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1104 X2 X1 X0 x X4
       have i₂ := eq2098 X0 X1 x X4
       grind)
    | exact superpose eq2098 eq1104
    | exact resolve eq1104 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq2237 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X4 (M.op X1 X2))) = (M.op X0 (M.op X4 (M.op X2 X1))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1105 X0 X1 X2 x X4
       have i₂ := eq2098 X2 X4 x X1
       grind)
    | exact superpose eq2098 eq1105
    | exact resolve eq1105 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105
  have eq2240 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X3 X4) (M.op X0 X2)) (M.op X0 (M.op X4 X2))) = X3 := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq426 X0 x X2 X3 X4
       have i₂ := eq2098 X0 (M.op X3 X4) x X2
       grind)
    | exact superpose eq2098 eq426
    | exact resolve eq426 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq2264 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X3 X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq974 X0 X1 X2 X3 X4 x
       have i₂ := eq2098 X4 (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4) x X3
       grind)
    | exact superpose eq2098 eq974
    | exact resolve eq974 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq2266 : ∀ X0 X2 : G, x = (M.op (M.op (M.op x y) (M.op X0 X2)) (M.op X0 (M.op y X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq430 X0 X2 x
       have i₂ := eq2098 X0 sF0 X2 x
       grind)
    | exact superpose eq2098 eq430
    | exact resolve eq430 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq2267 : ∀ X0 X2 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X2)) (M.op X0 (M.op (σ y) X2))) := by
    intro X0 X2
    first
    | (have i₁ := eq431 X0 X2 x
       have i₂ := eq2098 X0 sF4 X2 x
       grind)
    | exact superpose eq2098 eq431
    | exact resolve eq431 eq2098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq2098
  have eq2296 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op y (M.op x X1))) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1638 X0 X1 X2
       have i₂ := eq2096 y X0 x X1
       grind)
    | exact superpose eq2096 eq1638
    | exact resolve eq1638 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq2302 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ y) (M.op (σ x) X1))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2030 X1 x X2
       have i₂ := eq2096 sF3 X1 sF2 x
       grind)
    | exact superpose eq2096 eq2030
    | exact resolve eq2030 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030
  have eq2342 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 (M.op (M.op X1 X2) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq558 X0 X1 X2 X3 X4
       have i₂ := eq2096 X0 (M.op X3 (M.op X2 X4)) (M.op X1 X2) X1
       grind)
    | exact superpose eq2096 eq558
    | exact resolve eq558 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq2365 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 X4)) = (M.op (M.op (M.op (M.op X0 X1) X2) X3) (M.op X1 (M.op X4 X3))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1090 X0 X1 X2 X3 X4
       have i₂ := eq2096 X1 (M.op (M.op (M.op X0 X1) X2) X3) X4 X3
       grind)
    | exact superpose eq2096 eq1090
    | exact resolve eq1090 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq2370 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq1338 X0
       have i₂ := eq2096 X0 (M.op sF0 X0) x sF0
       grind)
    | exact superpose eq2096 eq1338
    | exact resolve eq1338 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq2371 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1717 X0
       have i₂ := eq2096 X0 (M.op sF4 X0) sF2 sF4
       grind)
    | exact superpose eq2096 eq1717
    | exact resolve eq1717 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq2374 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 x
       have i₂ := eq2096 X0 sF0 x y
       grind)
    | exact superpose eq2096 eq514
    | exact resolve eq514 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq2519 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x y) (M.op x (M.op (M.op x y) y))) := by
    first
    | (have i₁ := eq1351
       have i₂ := eq2374 x sF0
       grind)
    | exact superpose eq2374 eq1351
    | exact resolve eq1351 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1351 eq2374
  have eq2522 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq1697 eq2371
    | exact resolve eq2371 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2371
  have eq2523 : ∀ X0 : G, x = (M.op (M.op (M.op x y) X0) (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq1318 eq2370
    | exact resolve eq2370 eq1318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1318 eq2370
  have eq2543 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 (M.op X1 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2342 X0 X1 X2 X3 X4
       have i₂ := eq2237 (M.op X3 (M.op X2 X4)) (M.op X1 X2) X1 X0
       grind)
    | (have i₁ := eq2342 X0 X1 X2 X3 X4
       have i₂ := eq2237 (M.op X3 (M.op X2 X4)) X1 (M.op X1 X2) X0
       grind)
    | exact superpose eq2237 eq2342
    | exact resolve eq2342 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2342
  have eq2677 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x y) (M.op x (M.op y (M.op x y)))) := by
    first
    | (have i₁ := eq2519
       have i₂ := eq2237 sF0 sF0 y x
       grind)
    | (have i₁ := eq2519
       have i₂ := eq2237 sF0 y sF0 x
       grind)
    | exact superpose eq2237 eq2519
    | exact resolve eq2519 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq2693 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X0) X4) = (M.op (M.op X3 (M.op X2 X4)) (M.op X0 X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq2543 X0 x X2 X3 X4
       have i₂ := eq1147 X0 X2 x
       grind)
    | exact superpose eq1147 eq2543
    | exact resolve eq2543 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543
  have eq2750 : (M.op (M.op x y) (M.op y y)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq530 eq2677
    | exact resolve eq2677 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2677
  have eq2823 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq2522 eq53
    | exact resolve eq53 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2829 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 (M.op (M.op (σ x) (σ y)) X1))) X2) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2522 eq53
    | exact resolve eq53 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2838 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (M.op X1 (σ y))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq2829 X0 x X1
       have i₂ := eq512 X0 X1 sF4 x
       grind)
    | exact superpose eq512 eq2829
    | exact resolve eq2829 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2829
  have eq2876 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 (M.op (M.op x y) X1))) X2) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1 X2
    first
    | exact superpose eq2523 eq53
    | exact resolve eq53 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2885 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X0 (M.op X1 y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq2876 X0 x X1
       have i₂ := eq512 X0 X1 sF0 x
       grind)
    | exact superpose eq512 eq2876
    | exact resolve eq2876 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2876
  have eq2957 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq422 (M.op y x)
       have i₂ := eq1147 (M.op sF0 (M.op y x)) x y
       grind)
    | exact superpose eq1147 eq422
    | exact resolve eq422 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2958 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq423 (M.op sF3 x)
       have i₂ := eq1147 (M.op sF4 (M.op sF3 x)) x sF3
       grind)
    | exact superpose eq1147 eq423
    | exact resolve eq423 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq3073 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) (M.op y (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2957 eq414
    | exact resolve eq414 eq2957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3167 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2958 eq414
    | exact resolve eq414 eq2958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2958
  have eq3392 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op y y) X1)) = (M.op (M.op X0 (M.op (M.op x y) (M.op x x))) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq2750 eq53
    | exact resolve eq53 eq2750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2750
  have eq3401 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) (M.op (M.op y y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3392 X0 X1
       have i₂ := eq512 X0 sF0 x x
       grind)
    | exact superpose eq512 eq3392
    | exact resolve eq3392 eq512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512 eq3392
  have eq3414 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) (M.op y (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq3401 X0 X1
       have i₂ := eq2096 y (M.op X0 X1) y X1
       grind)
    | exact superpose eq2096 eq3401
    | exact resolve eq3401 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3401
  have eq3419 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3414 X0 X1
       have i₂ := eq1147 (M.op X0 X1) X1 y
       grind)
    | exact superpose eq1147 eq3414
    | exact resolve eq3414 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3414
  have eq3437 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 X4)) = (M.op X3 (M.op (M.op X2 X4) (M.op (M.op X0 (M.op X1 X2)) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq529 X3 (M.op X2 X4) (M.op X0 X4)
       have i₂ := eq53 X0 X4 X2 X1
       grind)
    | exact superpose eq53 eq529
    | exact resolve eq529 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3439 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq529 X1 (M.op X2 X3) (M.op (M.op X0 X2) X3)
       have i₂ := eq424 X0 X2 X3
       grind)
    | exact superpose eq424 eq529
    | exact resolve eq529 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3442 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq529 X3 X4 (M.op X0 (M.op X4 X2))
       have i₂ := eq53 X0 X1 X2 X4
       grind)
    | exact superpose eq53 eq529
    | exact resolve eq529 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3553 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 (M.op X1 (M.op X2 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3442 X0 X1 X2 X3 X4
       have i₂ := eq2096 X0 X4 X1 (M.op X2 X1)
       grind)
    | exact superpose eq2096 eq3442
    | exact resolve eq3442 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3442
  have eq3556 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3439 X0 X1 X2 X3
       have i₂ := eq2096 X2 X1 X3 X0
       grind)
    | exact superpose eq2096 eq3439
    | exact resolve eq3439 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439
  have eq3558 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 X4)) = (M.op X3 (M.op (M.op X2 X4) (M.op X1 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3437 X0 X1 X2 X3 X4
       have i₂ := eq2237 X3 (M.op X0 (M.op X1 X2)) X1 (M.op X2 X4)
       grind)
    | (have i₁ := eq3437 X0 X1 X2 X3 X4
       have i₂ := eq2237 X3 X1 (M.op X0 (M.op X1 X2)) (M.op X2 X4)
       grind)
    | exact superpose eq2237 eq3437
    | exact resolve eq3437 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3437
  have eq3584 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X0 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3553 X0 x X2 X3 X4
       have i₂ := eq529 X0 x X2
       grind)
    | exact superpose eq529 eq3553
    | exact resolve eq3553 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3553
  have eq3587 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X2 X3))) = (M.op X1 (M.op X2 (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3556 X0 X1 X2 X3
       have i₂ := eq2096 X0 X1 X2 X3
       grind)
    | exact superpose eq2096 eq3556
    | exact resolve eq3556 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3556
  have eq3590 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 X4)) = (M.op X3 (M.op X2 (M.op X4 (M.op X1 (M.op X0 (M.op X1 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3558 X0 X1 X2 X3 X4
       have i₂ := eq2096 X2 X3 X4 (M.op X1 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq2096 eq3558
    | exact resolve eq3558 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3558
  have eq3602 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op x (M.op y X1))) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2296 X0 X1 X2
       have i₂ := eq3584 y X1 X0 x
       grind)
    | (have i₁ := eq2296 X0 X1 X2
       have i₂ := eq3584 x X1 X0 y
       grind)
    | exact superpose eq3584 eq2296
    | exact resolve eq2296 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq3607 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ x) (M.op (σ y) X1))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2302 x X2 X2
       have i₂ := eq3584 sF3 X2 x sF2
       grind)
    | (have i₁ := eq2302 x X2 X2
       have i₂ := eq3584 sF2 X2 x sF3
       grind)
    | exact superpose eq3584 eq2302
    | exact resolve eq2302 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2302
  have eq3710 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op X3 (M.op X0 (M.op (M.op X4 X4) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2112 (M.op X0 (M.op (M.op X4 X4) X2)) X3 X4
       have i₂ := eq53 X0 X1 X2 (M.op X4 X4)
       grind)
    | exact superpose eq53 eq2112
    | exact resolve eq2112 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3723 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq414 X0 X1 (M.op X2 X2)
       have i₂ := eq2112 X1 X0 X2
       grind)
    | exact superpose eq2112 eq414
    | exact resolve eq414 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3724 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op (M.op X3 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X0 X2 (M.op X3 X3) X1
       have i₂ := eq2112 X1 X0 X3
       grind)
    | exact superpose eq2112 eq53
    | exact resolve eq53 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3743 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq424 X0 X1 (M.op X2 X2)
       have i₂ := eq2112 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X2
       grind)
    | exact superpose eq2112 eq424
    | exact resolve eq424 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3755 : ∀ X0 : G, x = (M.op (M.op (M.op x y) y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2957 (M.op x x)
       have i₂ := eq2112 y sF0 x
       grind)
    | exact superpose eq2112 eq2957
    | exact resolve eq2957 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2957
  have eq3792 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) (M.op X3 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3724 X0 X1 X2 X3
       have i₂ := eq2096 X3 (M.op X0 X2) X3 X2
       grind)
    | exact superpose eq2096 eq3724
    | exact resolve eq3724 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq3800 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op X3 (M.op X0 (M.op X4 (M.op X4 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3710 X0 X1 X2 X3 X4
       have i₂ := eq2096 X4 X0 X4 X2
       grind)
    | exact superpose eq2096 eq3710
    | exact resolve eq3710 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3710
  have eq3827 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3792 X0 X1 X2 x
       have i₂ := eq1147 (M.op X0 X2) X2 x
       grind)
    | exact superpose eq1147 eq3792
    | exact resolve eq3792 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3792
  have eq3831 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) (M.op X2 X1))) = (M.op X3 (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3800 X0 X1 X2 X3 x
       have i₂ := eq1147 X0 X2 x
       grind)
    | exact superpose eq1147 eq3800
    | exact resolve eq3800 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3800
  have eq3847 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X2)) = (M.op X3 (M.op X1 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3831 X0 X1 X2 X3
       have i₂ := eq3587 X1 X3 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq3831 X0 X3 X2 X1
       have i₂ := eq3587 (M.op X0 X3) X1 X2 X3
       grind)
    | exact superpose eq3587 eq3831
    | exact resolve eq3831 eq3587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3831
  have eq3851 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X2)) = (M.op X3 (M.op X1 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3847 X0 X1 X2 X3
       have i₂ := eq2096 X0 X1 X1 X2
       grind)
    | exact superpose eq2096 eq3847
    | exact resolve eq3847 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3847
  have eq3856 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 X4)) = (M.op X3 (M.op X2 (M.op X4 (M.op X0 X2)))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq3590 X0 x X2 X3 X4
       have i₂ := eq3851 X0 x X2 X4
       grind)
    | exact superpose eq3851 eq3590
    | exact resolve eq3590 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3590
  have eq4009 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op (M.op x y) y) X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq3755 eq53
    | exact resolve eq53 eq3755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq3755
  have eq4418 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 X1) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq651 eq2148
    | exact resolve eq2148 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4489 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq414 (M.op (M.op X0 X2) X1) X1 X2
       have i₂ := eq2148 X0 X2 X1
       grind)
    | exact superpose eq2148 eq414
    | exact resolve eq414 eq2148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq4558 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 X1) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq1337 X0 X1
       have i₂ := eq4489 X0 (M.op X1 y) X1
       grind)
    | (have i₁ := eq1337 X0 X1
       have i₂ := eq4489 X0 X1 (M.op X1 y)
       grind)
    | exact superpose eq4489 eq1337
    | exact resolve eq1337 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1337
  have eq4561 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1716 X0 x
       have i₂ := eq4489 X0 (M.op x sF3) x
       grind)
    | (have i₁ := eq1716 X0 X1
       have i₂ := eq4489 X0 X1 (M.op X1 sF3)
       grind)
    | exact superpose eq4489 eq1716
    | exact resolve eq1716 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1716
  have eq4587 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X0 x) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2885 X0 X1
       have i₂ := eq4489 X0 (M.op X1 y) x
       grind)
    | (have i₁ := eq2885 X0 X1
       have i₂ := eq4489 X0 x (M.op X1 y)
       grind)
    | exact superpose eq4489 eq2885
    | exact resolve eq2885 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2885
  have eq4593 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op x y)) (M.op x (M.op y X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3602 X0 X1 X2
       have i₂ := eq4489 X0 (M.op x (M.op y X1)) sF0
       grind)
    | (have i₁ := eq3602 X0 X1 X2
       have i₂ := eq4489 X0 sF0 (M.op x (M.op y X1))
       grind)
    | exact superpose eq4489 eq3602
    | exact resolve eq3602 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3602
  have eq4599 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2838 X0 X1
       have i₂ := eq4489 X0 (M.op X1 sF3) sF2
       grind)
    | (have i₁ := eq2838 X0 X1
       have i₂ := eq4489 X0 sF2 (M.op X1 sF3)
       grind)
    | exact superpose eq4489 eq2838
    | exact resolve eq2838 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2838
  have eq4604 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X1 X2)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3607 X0 X1 X2
       have i₂ := eq4489 X0 (M.op sF2 (M.op sF3 X1)) sF4
       grind)
    | (have i₁ := eq3607 X0 X1 X2
       have i₂ := eq4489 X0 sF4 (M.op sF2 (M.op sF3 X1))
       grind)
    | exact superpose eq4489 eq3607
    | exact resolve eq3607 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3607
  have eq6095 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X2 X1)) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3723 (M.op (M.op X0 X1) X2) (M.op X2 X1) X3
       have i₂ := eq2148 X0 X1 X2
       grind)
    | exact superpose eq2148 eq3723
    | exact resolve eq3723 eq2148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6101 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq651 eq3723
    | exact resolve eq3723 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6429 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 (M.op x y))) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq530 eq2266
    | exact resolve eq2266 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq2266
  have eq6526 : ∀ X0 : G, x = (M.op (M.op (M.op x y) (M.op X0 x)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq6429 X0
       have i₂ := eq4489 sF0 (M.op X0 sF0) (M.op X0 x)
       grind)
    | (have i₁ := eq6429 X0
       have i₂ := eq4489 sF0 (M.op X0 x) (M.op X0 sF0)
       grind)
    | exact superpose eq4489 eq6429
    | exact resolve eq6429 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6429
  have eq7055 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X3 X3)) (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3743 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3
       have i₂ := eq424 X0 X1 X2
       grind)
    | exact superpose eq424 eq3743
    | exact resolve eq3743 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7396 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq2522 eq3827
    | exact resolve eq3827 eq2522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7397 : ∀ X0 X1 : G, (M.op x (M.op X0 y)) = (M.op (M.op (M.op (M.op x y) X0) X1) X1) := by
    intro X0 X1
    first
    | exact superpose eq2523 eq3827
    | exact resolve eq3827 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7402 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) x) X1) = (M.op (M.op (M.op X0 X1) X2) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3827 (M.op X0 X1) X2 X1
       have i₂ := eq3419 X0 X1
       grind)
    | (have i₁ := eq3827 (M.op X0 x) X1 x
       have i₂ := eq3419 X0 X1
       grind)
    | exact superpose eq3419 eq3827
    | exact resolve eq3827 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7842 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X0 X2) X3) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4489 (M.op X0 X2) X3 X1
       have i₂ := eq4489 X0 X2 X1
       grind)
    | (have i₁ := eq4489 (M.op X0 X2) X3 X1
       have i₂ := eq4489 X0 X1 X2
       grind)
    | exact superpose eq4489 eq4489
    | exact resolve eq4489 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7848 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 x) X2) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4489 (M.op X0 x) X2 x
       have i₂ := eq3419 X0 X1
       grind)
    | (have i₁ := eq4489 (M.op X0 X1) X1 X1
       have i₂ := eq3419 X0 X1
       grind)
    | exact superpose eq3419 eq4489
    | exact resolve eq4489 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7852 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 (σ x)) (σ y)) X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq651 eq4489
    | exact resolve eq4489 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq7935 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op (M.op X0 X3) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2232 (M.op X0 X3) X1 X2
       have i₂ := eq4489 X0 X3 (M.op X1 X2)
       grind)
    | (have i₁ := eq2232 (M.op X0 X3) X1 X2
       have i₂ := eq4489 X0 (M.op X1 X2) X3
       grind)
    | exact superpose eq4489 eq2232
    | exact resolve eq2232 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8308 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op x y)) x)) = (M.op X0 (M.op (M.op x y) (M.op X1 x))) := by
    intro X0 X1
    first
    | exact superpose eq6526 eq529
    | exact resolve eq529 eq6526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526
  have eq8333 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op x y)) x)) = (M.op X0 (M.op x (M.op (M.op x y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq8308 X1 x
       have i₂ := eq3587 sF0 X1 x x
       grind)
    | (have i₁ := eq8308 X1 x
       have i₂ := eq3587 x X1 sF0 x
       grind)
    | exact superpose eq3587 eq8308
    | exact resolve eq8308 eq3587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8308
  have eq8379 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op x y)) x)) = (M.op X0 (M.op x (M.op x (M.op y X1)))) := by
    intro X0 X1
    first
    | exact superpose eq2092 eq8333
    | exact resolve eq8333 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8333
  have eq8413 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op X0 (M.op (M.op X1 (M.op x y)) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq8379 X0 X1
       have i₂ := eq1147 X0 (M.op y X1) x
       grind)
    | exact superpose eq1147 eq8379
    | exact resolve eq8379 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8379
  have eq8430 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op X0 (M.op x (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq8413 X0 X1
       have i₂ := eq2232 X0 (M.op X1 sF0) x
       grind)
    | (have i₁ := eq8413 X0 X1
       have i₂ := eq2232 X0 x (M.op X1 sF0)
       grind)
    | exact superpose eq2232 eq8413
    | exact resolve eq8413 eq2232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8413
  have eq10195 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 X2))) = (M.op X0 (M.op (M.op X1 (M.op (σ y) X2)) (σ x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2267 eq529
    | exact resolve eq529 eq2267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2267
  have eq10220 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 X2))) = (M.op X0 (M.op (σ x) (M.op X1 (M.op (σ y) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10195 X0 X1 X2
       have i₂ := eq2232 X0 (M.op X1 (M.op sF3 X2)) sF2
       grind)
    | (have i₁ := eq10195 X0 X1 X2
       have i₂ := eq2232 X0 sF2 (M.op X1 (M.op sF3 X2))
       grind)
    | exact superpose eq2232 eq10195
    | exact resolve eq10195 eq2232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10195
  have eq10342 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (M.op X1 (M.op (σ y) X2)))) = (M.op X0 (M.op (σ x) (M.op (σ y) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2093 eq10220
    | exact resolve eq10220 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10220
  have eq12896 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (M.op X0 (M.op (σ x) (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq2093 eq2232
    | exact resolve eq2232 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12920 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op (σ x) (σ y)) X1) X0)) = (M.op X2 (M.op X0 (M.op (σ x) (M.op (σ y) X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2093 eq2232
    | exact resolve eq2232 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13040 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X1 X0))) = (M.op X2 (M.op X0 (M.op (σ x) (M.op (σ y) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12920 x X2 X1
       have i₂ := eq2096 sF4 X1 X2 x
       grind)
    | exact superpose eq2096 eq12920
    | exact resolve eq12920 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12920
  have eq13140 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (M.op (σ y) (M.op X1 X0)))) = (M.op X2 (M.op X0 (M.op (σ x) (M.op (σ y) X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2093 eq13040
    | exact resolve eq13040 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13040
  have eq13674 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq136 (M.op y y)
       have i₂ := eq4558 y y
       grind)
    | exact superpose eq4558 eq136
    | exact resolve eq136 eq4558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13721 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq13674
       have i₂ := eq136 y
       grind)
    | exact superpose eq136 eq13674
    | exact resolve eq13674 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13674
  have eq13854 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq13721
       have i₂ := eq4604 (σ y) (σ y) (σ y)
       grind)
    | exact superpose eq4604 eq13721
    | exact resolve eq13721 eq4604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4604 eq13721
  have eq13957 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (M.op (σ y) (σ y))) (σ y))) := by
    first
    | exact superpose eq4599 eq13854
    | exact resolve eq13854 eq4599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13854
  have eq14027 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (M.op (σ y) (σ y))))) := by
    first
    | (have i₁ := eq13957
       have i₂ := eq2232 (M.op (σ y) sF2) (M.op sF2 (M.op sF3 (σ y))) sF3
       grind)
    | (have i₁ := eq13957
       have i₂ := eq2232 (M.op (σ y) sF2) sF3 (M.op sF2 (M.op sF3 (σ y)))
       grind)
    | exact superpose eq2232 eq13957
    | exact resolve eq13957 eq2232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13957
  have eq14079 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | (have i₁ := eq14027
       have i₂ := eq3584 sF3 (M.op sF3 (σ y)) (M.op (σ y) sF2) sF2
       grind)
    | (have i₁ := eq14027
       have i₂ := eq3584 sF2 (M.op sF3 (σ y)) (M.op (σ y) sF2) sF3
       grind)
    | exact superpose eq3584 eq14027
    | exact resolve eq14027 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14027
  have eq14115 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14079
       have i₂ := eq1147 sF2 (σ y) sF3
       grind)
    | exact superpose eq1147 eq14079
    | exact resolve eq14079 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14079
  have eq14143 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq14115
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14115
    | exact resolve eq14115 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14115
  have eq14165 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq4561 eq14143
    | exact resolve eq14143 eq4561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14143
  have eq14178 : (M.op (σ (M.op y x)) (σ (M.op y x))) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1679 eq14165
    | exact resolve eq14165 eq1679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14165
  have eq14187 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1679
       have i₂ := eq14178
       grind)
    | exact superpose eq14178 eq1679
    | exact resolve eq1679 eq14178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1679 eq14178
  have eq14421 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq1697 eq4561
    | exact resolve eq4561 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14445 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4561 (M.op (M.op X0 X1) (M.op X2 X2)) X1
       have i₂ := eq3743 X0 X1 X2
       grind)
    | exact superpose eq3743 eq4561
    | exact resolve eq4561 eq3743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4561
  have eq14640 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op (M.op (M.op X0 X1) (σ x)) (M.op (σ x) (σ y))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14445 X0 X1 X2
       have i₂ := eq7842 (M.op X0 X1) (M.op X2 X2) sF2 sF4
       grind)
    | (have i₁ := eq14445 X0 X1 X2
       have i₂ := eq7842 (M.op X0 X1) sF4 (M.op X2 X2) sF2
       grind)
    | exact superpose eq7842 eq14445
    | exact resolve eq14445 eq7842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14445
  have eq14659 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x y)) (M.op x (M.op y (M.op (σ x) (M.op (σ x) (σ y)))))) := by
    intro X0
    first
    | (have i₁ := eq14421 X0
       have i₂ := eq4593 X0 (M.op sF2 sF4) sF3
       grind)
    | exact superpose eq4593 eq14421
    | exact resolve eq14421 eq4593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4593 eq14421
  have eq14749 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op (M.op (M.op X0 X1) (σ x)) (σ x)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq6101 eq14640
    | exact resolve eq14640 eq6101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6101 eq14640
  have eq14767 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op x y)) (M.op x (M.op y (σ y)))) := by
    intro X0
    first
    | exact superpose eq1697 eq14659
    | exact resolve eq14659 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14659
  have eq14831 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op (M.op (M.op X0 X1) x) (σ y)) x) := by
    intro X0 X1
    first
    | (have i₁ := eq14749 X0 X1
       have i₂ := eq7848 (M.op X0 X1) sF2 sF3
       grind)
    | exact superpose eq7848 eq14749
    | exact resolve eq14749 eq7848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7848 eq14749
  have eq14870 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) (M.op x y)) (M.op x (M.op y (σ y)))) := by
    first
    | exact superpose eq14767 eq14187
    | exact resolve eq14187 eq14767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14187 eq14767
  have eq14939 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op (M.op (M.op (M.op X0 X1) x) x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14831 X0 X1
       have i₂ := eq7842 (M.op X0 X1) x sF3 x
       grind)
    | (have i₁ := eq14831 X0 X1
       have i₂ := eq7842 (M.op X0 X1) x x sF3
       grind)
    | exact superpose eq7842 eq14831
    | exact resolve eq14831 eq7842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14831
  have eq14961 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) x) (M.op (M.op x (M.op y (σ y))) y)) := by
    first
    | exact superpose eq4587 eq14870
    | exact resolve eq14870 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14870
  have eq15039 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) x) (M.op y (M.op x (M.op y (σ y))))) := by
    first
    | (have i₁ := eq14961
       have i₂ := eq2232 (M.op sF3 x) (M.op x (M.op y sF3)) y
       grind)
    | (have i₁ := eq14961
       have i₂ := eq2232 (M.op sF3 x) y (M.op x (M.op y sF3))
       grind)
    | exact superpose eq2232 eq14961
    | exact resolve eq14961 eq2232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14961
  have eq15109 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) x) (M.op x (M.op y (M.op y (σ y))))) := by
    first
    | (have i₁ := eq15039
       have i₂ := eq3584 y (M.op y sF3) (M.op sF3 x) x
       grind)
    | (have i₁ := eq15039
       have i₂ := eq3584 x (M.op y sF3) (M.op sF3 x) y
       grind)
    | exact superpose eq3584 eq15039
    | exact resolve eq15039 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15039
  have eq15170 : (σ (M.op (M.op y x) (M.op x y))) = (M.op (M.op (σ y) x) (M.op x (σ y))) := by
    first
    | (have i₁ := eq15109
       have i₂ := eq1147 x sF3 y
       grind)
    | exact superpose eq1147 eq15109
    | exact resolve eq15109 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15109
  have eq15417 : ∀ X0 : G, (σ (M.op (M.op y x) (M.op x y))) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq136 (M.op y X0)
       have i₂ := eq1303 y X0
       grind)
    | exact superpose eq1303 eq136
    | exact resolve eq136 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq15504 : ∀ X0 : G, (M.op (M.op (σ y) x) (M.op x (σ y))) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq15170 eq15417
    | exact resolve eq15417 eq15170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15170 eq15417
  have eq17500 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op y (M.op X0 (M.op x X0))))) := by
    intro X0
    first
    | (have i₁ := eq136 (M.op x X0)
       have i₂ := eq3073 X0 (M.op x X0)
       grind)
    | exact superpose eq3073 eq136
    | exact resolve eq136 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17521 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) (M.op y (M.op X0 X1))) (M.op X2 X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3743 (M.op x X0) X1 X2
       have i₂ := eq3073 X0 X1
       grind)
    | exact superpose eq3073 eq3743
    | exact resolve eq3743 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17590 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X1) (M.op y (M.op X0 X1))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17521 X0 x X2
       have i₂ := eq7842 sF0 (M.op y (M.op X0 x)) (M.op X2 X2) x
       grind)
    | (have i₁ := eq17521 X0 X1 X2
       have i₂ := eq7842 sF0 X1 (M.op y (M.op X0 X1)) (M.op X2 X2)
       grind)
    | exact superpose eq7842 eq17521
    | exact resolve eq17521 eq7842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7842 eq17521
  have eq17608 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op y x))) := by
    intro X0
    first
    | (have i₁ := eq17500 X0
       have i₂ := eq529 y X0 x
       grind)
    | exact superpose eq529 eq17500
    | exact resolve eq17500 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17500
  have eq17683 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X1) (M.op X0 X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq17590 X0 X1 x
       have i₂ := eq6095 (M.op sF0 X1) (M.op X0 X1) y x
       grind)
    | exact superpose eq6095 eq17590
    | exact resolve eq17590 eq6095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6095 eq17590
  have eq17701 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op x (M.op x (M.op x y))))) := by
    intro X0
    first
    | (have i₁ := eq17608 X0
       have i₂ := eq8430 sF0 x
       grind)
    | exact superpose eq8430 eq17608
    | exact resolve eq17608 eq8430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8430 eq17608
  have eq17757 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op (M.op (M.op x y) X1) y) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17683 X1 x
       have i₂ := eq7935 (M.op sF0 x) X1 x y
       grind)
    | exact superpose eq7935 eq17683
    | exact resolve eq17683 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17683
  have eq17773 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq17701 X0
       have i₂ := eq1147 sF0 sF0 x
       grind)
    | exact superpose eq1147 eq17701
    | exact resolve eq17701 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17701
  have eq17837 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq17773 X0
       have i₂ := eq136 sF0
       grind)
    | exact superpose eq136 eq17773
    | exact resolve eq17773 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17773
  have eq17869 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq20 eq17837
    | (have j0 := eq17837 X0
       grind)
    | exact resolve eq17837 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17837
  have eq18520 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 (M.op x y)) x) (M.op X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4587 (M.op X0 sF0) X1
       have i₂ := eq3827 X0 sF0 X2
       grind)
    | (have i₁ := eq4587 (M.op X0 sF0) X1
       have i₂ := eq3827 X0 X1 sF0
       grind)
    | exact superpose eq3827 eq4587
    | exact resolve eq4587 eq3827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18609 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op X0 x) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq4587 eq4489
    | exact resolve eq4489 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18698 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) X1) = (M.op (M.op X0 x) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2232 (M.op X0 x) X1 y
       have i₂ := eq4587 X0 X1
       grind)
    | exact superpose eq4587 eq2232
    | exact resolve eq2232 eq4587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq18965 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op X2 y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18520 X0 X1 X2
       have i₂ := eq4489 X0 sF0 x
       grind)
    | (have i₁ := eq18520 X0 X1 X2
       have i₂ := eq4489 X0 x sF0
       grind)
    | exact superpose eq4489 eq18520
    | exact resolve eq18520 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18520
  have eq19157 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 x) x) (M.op y (M.op X2 y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq18698 eq18965
    | exact resolve eq18965 eq18698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18965
  have eq19285 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) X2) = (M.op (M.op (M.op X0 x) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19157 X0 X1 X2
       have i₂ := eq529 (M.op (M.op X0 x) x) y X2
       grind)
    | exact superpose eq529 eq19157
    | exact resolve eq19157 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19157
  have eq19753 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq4599 eq4489
    | exact resolve eq4489 eq4599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4599
  have eq23848 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ x) (M.op (σ y) X1))))) = (M.op (M.op (σ x) X0) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq12896 eq3167
    | exact resolve eq3167 eq12896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23872 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq12896 eq3167
    | exact resolve eq3167 eq12896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23895 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (M.op (M.op (σ y) X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23872 X0 x
       have i₂ := eq2096 sF2 sF3 (M.op sF3 X0) x
       grind)
    | exact superpose eq2096 eq23872
    | exact resolve eq23872 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23872
  have eq23916 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ x) (M.op (σ y) X1))))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op X1 (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq3167 eq23848
    | exact resolve eq23848 eq3167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23848
  have eq24075 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (M.op (σ y) X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23895 X0 X1
       have i₂ := eq3584 sF3 (M.op (M.op sF3 X0) X1) sF4 sF2
       grind)
    | (have i₁ := eq23895 X0 X1
       have i₂ := eq3584 sF2 (M.op (M.op sF3 X0) X1) sF4 sF3
       grind)
    | exact superpose eq3584 eq23895
    | exact resolve eq23895 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23895
  have eq24191 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ y) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq24075 x x
       have i₂ := eq2096 sF3 sF3 x x
       grind)
    | exact superpose eq2096 eq24075
    | exact resolve eq24075 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24075
  have eq24282 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) X1) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24191 X0 X1
       have i₂ := eq1147 sF2 (M.op X0 X1) sF3
       grind)
    | exact superpose eq1147 eq24191
    | exact resolve eq24191 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24191
  have eq24342 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) X1))) := by
    intro X0 X1
    first
    | exact superpose eq3167 eq24282
    | exact resolve eq24282 eq3167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24282
  have eq24380 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (M.op (σ x) (σ y)) X1)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq24342 X0 x
       have i₂ := eq2096 X0 sF3 sF4 x
       grind)
    | exact superpose eq2096 eq24342
    | exact resolve eq24342 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24342
  have eq24405 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ x) (M.op (σ y) X1))))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) := by
    intro X0 X1
    first
    | exact superpose eq2093 eq24380
    | exact resolve eq24380 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24380
  have eq24424 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X1))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op X1 (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq24405 eq23916
    | exact resolve eq23916 eq24405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23916 eq24405
  have eq24559 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 (M.op X2 X2)) (M.op (σ x) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1259 eq3743
    | exact resolve eq3743 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24561 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (M.op X1 (M.op (σ x) (σ y))))) = (M.op (M.op (M.op (M.op X0 X1) (σ y)) X2) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1259 eq3827
    | exact resolve eq3827 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq24568 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op X1 (M.op (σ x) (σ y))))) = (M.op (M.op (M.op (M.op X0 X1) x) x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq24561 X0 X1 x
       have i₂ := eq7402 (M.op X0 X1) sF3 x
       grind)
    | exact superpose eq7402 eq24561
    | exact resolve eq24561 eq7402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24561
  have eq24570 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24559 X0 X1 x
       have i₂ := eq7055 X0 sF2 (M.op X1 sF4) x
       grind)
    | exact superpose eq7055 eq24559
    | exact resolve eq24559 eq7055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24559
  have eq24673 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op (σ x) (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq14939 eq24568
    | exact resolve eq24568 eq14939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14939 eq24568
  have eq25209 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (σ x) X0) y) (M.op x (M.op (M.op (σ y) X1) (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq2823 eq1278
    | exact resolve eq1278 eq2823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823
  have eq25289 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 (M.op X2 X2)) (M.op x (M.op X1 (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1278 eq3743
    | exact resolve eq3743 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1278
  have eq25300 : ∀ X0 X1 : G, (M.op (M.op X0 X1) y) = (M.op (M.op X0 x) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq25289 X0 X1 x
       have i₂ := eq7055 X0 x (M.op X1 sF0) x
       grind)
    | exact superpose eq7055 eq25289
    | exact resolve eq25289 eq7055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7055 eq25289
  have eq25374 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (σ x) X0) y) (M.op x (M.op (M.op x y) (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25209 X0 X1
       have i₂ := eq2237 (M.op (M.op sF2 X0) y) (M.op sF3 X1) sF0 x
       grind)
    | (have i₁ := eq25209 X0 X1
       have i₂ := eq2237 (M.op (M.op sF2 X0) y) sF0 (M.op sF3 X1) x
       grind)
    | exact superpose eq2237 eq25209
    | exact resolve eq25209 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25209
  have eq25474 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (σ x) X0) y) (M.op x (M.op x (M.op y (M.op (σ y) X1))))) := by
    intro X0 X1
    first
    | exact superpose eq2092 eq25374
    | exact resolve eq25374 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25374
  have eq25576 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (σ x) X0) y) (M.op y (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25474 X0 X1
       have i₂ := eq1147 (M.op (M.op sF2 X0) y) (M.op y (M.op sF3 X1)) x
       grind)
    | exact superpose eq1147 eq25474
    | exact resolve eq25474 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25474
  have eq25659 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 y))) (M.op y (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq3167 eq25576
    | exact resolve eq25576 eq3167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25576
  have eq25734 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op y (M.op (σ y) X0))) (M.op y (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq25659 x X1
       have i₂ := eq3587 sF3 sF4 x y
       grind)
    | (have i₁ := eq25659 x X1
       have i₂ := eq3587 y sF4 sF3 x
       grind)
    | exact superpose eq3587 eq25659
    | exact resolve eq25659 eq3587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3587 eq25659
  have eq26086 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) y) X1) = (M.op (M.op (M.op x X0) (M.op X0 X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq4009 eq3723
    | exact resolve eq3723 eq4009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4009
  have eq26101 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) y) X1) = (M.op (M.op (M.op x y) (M.op y (M.op X0 (M.op X0 X1)))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26086 X0 X1 X2
       have i₂ := eq3073 X0 (M.op X0 X1)
       grind)
    | exact superpose eq3073 eq26086
    | exact resolve eq26086 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26086
  have eq26216 : ∀ X1 X2 : G, (M.op (M.op (M.op x y) y) X1) = (M.op (M.op (M.op x y) (M.op y X1)) (M.op X2 X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq26101 x X1 X2
       have i₂ := eq1147 y X1 x
       grind)
    | exact superpose eq1147 eq26101
    | exact resolve eq26101 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26101
  have eq27314 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (σ x)) (σ y)) = (M.op X0 (M.op (M.op X2 X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4418 (M.op (M.op X0 X1) X2) (M.op X2 X1)
       have i₂ := eq2148 X0 X1 X2
       grind)
    | exact superpose eq2148 eq4418
    | exact resolve eq4418 eq2148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27535 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (σ x)) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27314 X0 X1 X2
       have i₂ := eq2232 X0 (M.op X2 X1) sF4
       grind)
    | (have i₁ := eq27314 X0 X1 X2
       have i₂ := eq2232 X0 sF4 (M.op X2 X1)
       grind)
    | exact superpose eq2232 eq27314
    | exact resolve eq27314 eq2232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27314
  have eq27662 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op X2 X1)))) = (M.op (M.op (M.op (M.op X0 X1) X2) (σ x)) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2093 eq27535
    | exact resolve eq27535 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27535
  have eq28702 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (σ x) (M.op X0 (σ y))) X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq7396 eq3723
    | exact resolve eq3723 eq7396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28708 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (M.op X0 (σ y))) (M.op X1 (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq7396 eq4418
    | exact resolve eq4418 eq7396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7396
  have eq28787 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op X0 (σ y)) (M.op X1 (M.op (σ x) (σ y)))))) := by
    intro X0 X1
    first
    | exact superpose eq3167 eq28708
    | exact resolve eq28708 eq3167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28708
  have eq28793 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op X0 (σ y)) X1))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq3167 eq28702
    | exact resolve eq28702 eq3167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28702
  have eq28901 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (M.op X0 (σ y)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq24424 eq28787
    | exact resolve eq28787 eq24424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24424 eq28787
  have eq28907 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op X0 (M.op (σ y) X1)))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28793 X0 x X2
       have i₂ := eq2096 X0 sF3 sF3 x
       grind)
    | exact superpose eq2096 eq28793
    | exact resolve eq28793 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28793
  have eq28989 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X1) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28901 X0 x
       have i₂ := eq2096 X0 sF2 sF3 x
       grind)
    | exact superpose eq2096 eq28901
    | exact resolve eq28901 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28901
  have eq28993 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28907 X0 X2 X2
       have i₂ := eq3851 X0 sF3 X2 sF4
       grind)
    | exact superpose eq3851 eq28907
    | exact resolve eq28907 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28907
  have eq29044 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op X1 X0)))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq27662 eq28989
    | exact resolve eq28989 eq27662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28989
  have eq29210 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op x (M.op X0 y)) X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq7397 eq3723
    | exact resolve eq3723 eq7397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7397
  have eq29301 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op x y) (M.op y (M.op (M.op X0 y) X1))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29210 X0 X1 X2
       have i₂ := eq3073 (M.op X0 y) X1
       grind)
    | exact superpose eq3073 eq29210
    | exact resolve eq29210 eq3073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3073 eq29210
  have eq29415 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op x y) y) (M.op (M.op X0 y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq26216 eq29301
    | exact resolve eq29301 eq26216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26216 eq29301
  have eq29499 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op x y) y) (M.op X0 (M.op y X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq29415 X0 x
       have i₂ := eq2096 X0 (M.op sF0 y) y x
       grind)
    | exact superpose eq2096 eq29415
    | exact resolve eq29415 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29415
  have eq33397 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op X2 (M.op (M.op (M.op X0 (σ x)) (σ y)) X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq7852 eq529
    | exact resolve eq529 eq7852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7852
  have eq33429 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op X2 (M.op (M.op X0 (σ x)) (M.op (σ y) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33397 X0 x X1
       have i₂ := eq2096 (M.op X0 sF2) X1 sF3 x
       grind)
    | exact superpose eq2096 eq33397
    | exact resolve eq33397 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33397
  have eq33500 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op X2 (M.op (σ y) (M.op (M.op X0 (σ x)) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33429 X0 X2 x
       have i₂ := eq3584 (M.op X0 sF2) X2 x sF3
       grind)
    | (have i₁ := eq33429 X0 X2 x
       have i₂ := eq3584 sF3 X2 x (M.op X0 sF2)
       grind)
    | exact superpose eq3584 eq33429
    | exact resolve eq33429 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33429
  have eq33547 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) = (M.op X2 (M.op (σ y) (M.op X0 (M.op (σ x) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33500 X0 x X2
       have i₂ := eq2096 X0 sF3 sF2 x
       grind)
    | exact superpose eq2096 eq33500
    | exact resolve eq33500 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33500
  have eq33578 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ x) (M.op (σ y) (M.op X0 X1)))) = (M.op X2 (M.op (σ y) (M.op X0 (M.op (σ x) X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2093 eq33547
    | exact resolve eq33547 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33547
  have eq37794 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op (M.op (M.op x y) X0) y) X1) := by
    intro X0 X1
    first
    | exact superpose eq17757 eq1147
    | exact resolve eq1147 eq17757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17757
  have eq38810 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq17869 x
       have i₂ := eq136 x
       grind)
    | exact superpose eq136 eq17869
    | exact resolve eq17869 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17869
  have eq38853 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq38810
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq38810
    | exact resolve eq38810 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38810
  have eq38861 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq3167 eq38853
    | exact resolve eq38853 eq3167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3167 eq38853
  have eq38867 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ x))))) := by
    first
    | exact superpose eq33578 eq38861
    | exact resolve eq38861 eq33578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38861
  have eq38871 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ x))))) := by
    first
    | exact superpose eq29044 eq38867
    | exact resolve eq38867 eq29044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29044 eq38867
  have eq38875 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq38871
       have i₂ := eq3856 sF2 x sF4 (M.op sF2 (M.op sF3 sF2))
       grind)
    | (have i₁ := eq38871
       have i₂ := eq3856 sF3 sF2 sF4 sF2
       grind)
    | exact superpose eq3856 eq38871
    | exact resolve eq38871 eq3856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3856 eq38871
  have eq38880 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq38875
       have i₂ := eq2232 sF4 sF3 sF2
       grind)
    | (have i₁ := eq38875
       have i₂ := eq2232 sF4 sF2 sF3
       grind)
    | exact superpose eq2232 eq38875
    | exact resolve eq38875 eq2232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38875
  have eq38883 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq38880
    | exact resolve eq38880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38880
  have eq38944 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq38883 eq2522
    | exact resolve eq2522 eq38883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2522
  have eq38955 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq38883 eq237
    | exact resolve eq237 eq38883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38969 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq38883 eq2148
    | exact resolve eq2148 eq38883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38883
  have eq39013 : (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq38955
       have i₂ := eq237 sF1
       grind)
    | exact superpose eq237 eq38955
    | exact resolve eq38955 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38955
  have eq39022 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq2093 eq38944
    | exact resolve eq38944 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093 eq38944
  have eq39042 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq37 eq39013
    | exact resolve eq39013 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39013
  have eq39048 : (σ x) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | (have i₁ := eq39022
       have i₂ := eq2112 sF2 (M.op sF1 sF1) sF3
       grind)
    | exact superpose eq2112 eq39022
    | exact resolve eq39022 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39022
  have eq39290 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq39048 eq424
    | exact resolve eq424 eq39048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39048
  have eq39379 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op X0 (M.op (σ (M.op x y)) (σ x)))) := by
    intro X0
    first
    | exact superpose eq39290 eq2148
    | exact resolve eq2148 eq39290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39290
  have eq39791 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) (M.op x y)) (M.op X0 X0)) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq39042 eq3743
    | exact resolve eq3743 eq39042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3743 eq39042
  have eq39813 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) y) (M.op (M.op x y) (M.op y (M.op X0 X0)))) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq29499 eq39791
    | exact resolve eq39791 eq29499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39791
  have eq39832 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) y) (M.op x (M.op y (M.op y (M.op X0 X0))))) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq2092 eq39813
    | exact resolve eq39813 eq2092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2092 eq39813
  have eq39849 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) x) (M.op y (M.op X0 X0))) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq29499 eq39832
    | exact resolve eq39832 eq29499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29499 eq39832
  have eq39861 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (M.op (M.op x y) x) y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq39849 x
       have i₂ := eq2112 y (M.op sF0 x) x
       grind)
    | exact superpose eq2112 eq39849
    | exact resolve eq39849 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39849
  have eq39868 : (τ (M.op (σ x) (σ y))) = (M.op x (M.op x (τ (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq37794 eq39861
    | exact resolve eq39861 eq37794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37794 eq39861
  have eq40277 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq38969 eq4418
    | exact resolve eq4418 eq38969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4418 eq38969
  have eq40286 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ x)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq40277 X0
       have i₂ := eq2096 X0 sF4 sF4 sF4
       grind)
    | exact superpose eq2096 eq40277
    | exact resolve eq40277 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40277
  have eq40359 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40286 X0
       have i₂ := eq2112 X0 sF4 sF4
       grind)
    | exact superpose eq2112 eq40286
    | exact resolve eq40286 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40286
  have eq40418 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X0 (σ (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq27662 eq40359
    | exact resolve eq40359 eq27662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27662 eq40359
  have eq40468 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) := by
    intro X0
    first
    | exact superpose eq13140 eq40418
    | exact resolve eq40418 eq13140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13140 eq40418
  have eq40534 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op y (M.op (σ y) X0))) (M.op y (M.op (σ y) X1))) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) := by
    intro X0 X1
    first
    | exact superpose eq40468 eq25734
    | exact resolve eq25734 eq40468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25734
  have eq40543 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (M.op X2 X2)) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq40468 eq28993
    | exact resolve eq28993 eq40468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28993
  have eq40760 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X0 X1))))) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq40468 eq40543
    | exact resolve eq40543 eq40468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40543
  have eq40764 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op y (M.op (σ y) X0)))))) (M.op y (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq40468 eq40534
    | exact resolve eq40534 eq40468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40534
  have eq40857 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op y (M.op (σ y) (M.op (σ y) X0)))))) (M.op y (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | exact superpose eq10342 eq40764
    | exact resolve eq40764 eq10342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40764
  have eq40918 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op y (M.op (σ x) (M.op (σ y) (M.op (σ y) X0)))))) (M.op y (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40857 X0 X1
       have i₂ := eq3584 sF2 (M.op sF3 (M.op sF3 X0)) sF1 y
       grind)
    | (have i₁ := eq40857 X0 X1
       have i₂ := eq3584 y (M.op sF3 (M.op sF3 X0)) sF1 sF2
       grind)
    | exact superpose eq3584 eq40857
    | exact resolve eq40857 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40857
  have eq40958 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (σ y) X0)))))) (M.op y (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40918 X0 X1
       have i₂ := eq3584 sF1 (M.op sF2 (M.op sF3 (M.op sF3 X0))) sF1 y
       grind)
    | (have i₁ := eq40918 X0 X1
       have i₂ := eq3584 y (M.op sF2 (M.op sF3 (M.op sF3 X0))) sF1 sF1
       grind)
    | exact superpose eq3584 eq40918
    | exact resolve eq40918 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40918
  have eq40991 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) X0)))) (M.op y (M.op (σ y) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40958 X1 X1
       have i₂ := eq1147 sF2 X1 sF3
       grind)
    | exact superpose eq1147 eq40958
    | exact resolve eq40958 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40958
  have eq41034 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X0 X1))))) (M.op X2 X2)) = (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) X0)))) (M.op y (M.op (σ y) X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq40991 eq40760
    | exact resolve eq40760 eq40991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40760
  have eq41084 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) X0)))) (M.op y (M.op (σ y) X1))) = (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X1))))) (M.op y (M.op (σ y) (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq40991 eq41034
    | exact resolve eq41034 eq40991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41034
  have eq41105 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) X0)))) (M.op y (M.op (σ y) X1))) = (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X1))))) (M.op y (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq41084 X0 X1 x
       have i₂ := eq2112 sF3 y x
       grind)
    | exact superpose eq2112 eq41084
    | exact resolve eq41084 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41084
  have eq41120 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) X0)))) (M.op y (M.op (σ y) X1))) = (M.op (M.op (σ (M.op x y)) (M.op y (σ y))) (M.op (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X1))) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq41105 X0 X1
       have i₂ := eq7935 sF1 y (M.op sF1 (M.op sF2 (M.op X0 X1))) (M.op y sF3)
       grind)
    | (have i₁ := eq41105 X0 X1
       have i₂ := eq7935 sF1 sF3 y (M.op y (M.op sF1 (M.op sF2 (M.op X0 X1))))
       grind)
    | exact superpose eq7935 eq41105
    | exact resolve eq41105 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41105
  have eq41133 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) X0)))) (M.op y (M.op (σ y) X1))) = (M.op (M.op (σ (M.op x y)) (M.op y (σ y))) (M.op (σ (M.op x y)) (M.op (M.op (σ x) (M.op X0 X1)) y))) := by
    intro X0 X1
    first
    | (have i₁ := eq41120 X0 X1
       have i₂ := eq2096 sF1 (M.op sF1 (M.op y sF3)) (M.op sF2 (M.op X0 X1)) y
       grind)
    | exact superpose eq2096 eq41120
    | exact resolve eq41120 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41120
  have eq41145 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) X0)))) (M.op y (M.op (σ y) X1))) = (M.op (M.op (σ (M.op x y)) (M.op y (σ y))) (M.op (σ (M.op x y)) (M.op y (M.op (σ x) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq41133 X0 X1
       have i₂ := eq2237 (M.op sF1 (M.op y sF3)) (M.op sF2 (M.op X0 X1)) y sF1
       grind)
    | (have i₁ := eq41133 X0 X1
       have i₂ := eq2237 (M.op sF1 (M.op y sF3)) y (M.op sF2 (M.op X0 X1)) sF1
       grind)
    | exact superpose eq2237 eq41133
    | exact resolve eq41133 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41133
  have eq41154 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) X0)))) (M.op y (M.op (σ y) X1))) = (M.op (M.op (σ (M.op x y)) (M.op y (σ y))) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq41145 X0 X1
       have i₂ := eq3584 sF1 (M.op sF2 (M.op X0 X1)) (M.op sF1 (M.op y sF3)) y
       grind)
    | (have i₁ := eq41145 X0 X1
       have i₂ := eq3584 y (M.op sF2 (M.op X0 X1)) (M.op sF1 (M.op y sF3)) sF1
       grind)
    | exact superpose eq3584 eq41145
    | exact resolve eq41145 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41145
  have eq41162 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) (M.op y (σ y))) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X1))))) := by
    intro X0 X1
    first
    | exact superpose eq41154 eq40991
    | exact resolve eq40991 eq41154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40991 eq41154
  have eq46618 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op X0 x) (M.op y X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2232 (M.op X0 x) X1 y
       have i₂ := eq18609 X0 X1
       grind)
    | (have i₁ := eq2232 (M.op X0 X1) x y
       have i₂ := eq18609 X0 X1
       grind)
    | exact superpose eq18609 eq2232
    | exact resolve eq2232 eq18609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232 eq18609
  have eq49075 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X2 (M.op X1 X3))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2236 X2 X0 X3 (M.op X1 X3)
       have i₂ := eq529 X0 X3 X1
       grind)
    | exact superpose eq529 eq2236
    | exact resolve eq2236 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49084 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) X2) = (M.op (M.op X0 (M.op X2 (M.op (σ y) X1))) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq12896 eq2236
    | exact resolve eq2236 eq12896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12896
  have eq49668 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) X2) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ y) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49084 X0 X1 X1
       have i₂ := eq7935 X0 X1 (M.op sF3 X1) sF2
       grind)
    | exact superpose eq7935 eq49084
    | exact resolve eq49084 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49084
  have eq49675 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) (M.op (M.op X1 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49075 X0 X1 X2 X3
       have i₂ := eq7935 X0 X2 (M.op X1 X3) X3
       grind)
    | (have i₁ := eq49075 X0 X1 X2 (M.op X2 X1)
       have i₂ := eq7935 X0 X1 X2 (M.op X2 (M.op X1 (M.op X2 X1)))
       grind)
    | exact superpose eq7935 eq49075
    | exact resolve eq49075 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49075
  have eq50168 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op X1 X2))) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49668 X0 X2 x
       have i₂ := eq2096 sF3 (M.op X0 sF2) X2 x
       grind)
    | exact superpose eq2096 eq49668
    | exact resolve eq49668 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49668
  have eq50173 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) (M.op X1 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq49675 X0 X1 X2 X3
       have i₂ := eq2096 X1 (M.op X0 X3) X3 X2
       grind)
    | exact superpose eq2096 eq49675
    | exact resolve eq49675 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49675
  have eq54267 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (M.op X1 (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq19753 eq529
    | exact resolve eq529 eq19753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54393 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op (M.op X0 (σ x)) (M.op X1 (σ y)))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq40468 eq54267
    | exact resolve eq54267 eq40468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54267
  have eq54566 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op (σ x) (M.op (σ y) (M.op (M.op X0 (σ x)) (M.op X1 (σ y)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54393 X0 X1 X0
       have i₂ := eq1147 X0 (M.op sF2 (M.op sF3 (M.op (M.op X0 sF2) (M.op X1 sF3)))) sF1
       grind)
    | exact superpose eq1147 eq54393
    | exact resolve eq54393 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54393
  have eq54704 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op (σ x) (M.op (σ y) (M.op X0 (M.op (σ x) (M.op X1 (σ y))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54566 X0 X1 X2
       have i₂ := eq2096 X0 sF3 sF2 (M.op X1 sF3)
       grind)
    | exact superpose eq2096 eq54566
    | exact resolve eq54566 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54566
  have eq54817 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op (σ x) (M.op (σ x) (M.op (σ y) (M.op X0 (M.op X1 (σ y))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq33578 eq54704
    | exact resolve eq54704 eq33578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54704
  have eq54893 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op (σ y) (M.op X0 (M.op X1 (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54817 X0 X1 X0
       have i₂ := eq1147 X0 (M.op sF3 (M.op X0 (M.op X1 sF3))) sF2
       grind)
    | exact superpose eq1147 eq54817
    | exact resolve eq54817 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54817
  have eq61016 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 (σ x)) (M.op X1 (M.op (σ x) (σ y)))) (M.op X3 (σ y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq24570 eq413
    | exact resolve eq413 eq24570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq24570
  have eq61153 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (M.op (σ y) (M.op X1 (M.op X3 (σ y))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq50168 eq61016
    | exact resolve eq61016 eq50168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50168 eq61016
  have eq61358 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) x) (M.op (σ y) (M.op X1 (M.op X3 (σ y))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61153 X0 X1 X2 X3
       have i₂ := eq19285 X0 sF2 (M.op sF3 (M.op X1 (M.op X3 sF3)))
       grind)
    | exact superpose eq19285 eq61153
    | exact resolve eq61153 eq19285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19285 eq61153
  have eq61525 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) x) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq54893 eq61358
    | exact resolve eq61358 eq54893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54893 eq61358
  have eq62129 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (σ y))) X2) = (M.op (M.op X0 (M.op X2 (M.op X1 (M.op (σ x) (σ y))))) (σ x)) := by
    intro X0 X1 X2
    first
    | exact superpose eq24673 eq2236
    | exact resolve eq2236 eq24673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24673
  have eq62324 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (σ y))) X2) = (M.op (M.op X0 (σ x)) (M.op (M.op X1 (M.op (σ x) (σ y))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62129 X0 X1 X1
       have i₂ := eq7935 X0 X1 (M.op X1 sF4) sF2
       grind)
    | exact superpose eq7935 eq62129
    | exact resolve eq62129 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62129
  have eq62436 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (σ y))) X2) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (M.op (σ x) (σ y)) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62324 X0 X0 x
       have i₂ := eq2096 X0 (M.op X0 sF2) sF4 x
       grind)
    | exact superpose eq2096 eq62324
    | exact resolve eq62324 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62324
  have eq62536 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (σ y))) X2) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X2)))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq40468 eq62436
    | exact resolve eq62436 eq40468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62436
  have eq62622 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (σ y))) X2) = (M.op (M.op X0 (σ x)) (M.op X1 (M.op (σ x) (M.op (σ y) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62536 X0 X0 X2
       have i₂ := eq1147 X0 (M.op sF2 (M.op sF3 X2)) sF1
       grind)
    | exact superpose eq1147 eq62536
    | exact resolve eq62536 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62536
  have eq62723 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op y (M.op (σ x) (M.op (σ y) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X1)))))))) := by
    intro X0 X1
    first
    | exact superpose eq62622 eq41162
    | exact resolve eq41162 eq62622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41162 eq62622
  have eq62818 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) y) (M.op (σ y) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq62723 X0 X1
       have i₂ := eq50173 sF1 y (M.op sF3 (M.op y (M.op sF1 (M.op sF2 (M.op X0 X1))))) sF2
       grind)
    | exact superpose eq50173 eq62723
    | exact resolve eq62723 eq50173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50173 eq62723
  have eq62904 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) y) (M.op y (M.op (σ y) (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq62818 X0 X1
       have i₂ := eq3584 sF3 (M.op sF1 (M.op sF2 (M.op X0 X1))) (M.op sF1 y) y
       grind)
    | (have i₁ := eq62818 X0 X1
       have i₂ := eq3584 y (M.op sF1 (M.op sF2 (M.op X0 X1))) (M.op sF1 y) sF3
       grind)
    | exact superpose eq3584 eq62818
    | exact resolve eq62818 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62818
  have eq62984 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) y) (M.op y (M.op (σ x) (M.op (σ y) (M.op (σ (M.op x y)) (M.op X0 X1)))))) := by
    intro X0 X1
    first
    | exact superpose eq33578 eq62904
    | exact resolve eq62904 eq33578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33578 eq62904
  have eq63046 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) y) (M.op y (M.op (σ x) (M.op (σ (M.op x y)) (M.op (σ y) (M.op X0 X1)))))) := by
    intro X0 X1
    first
    | exact superpose eq10342 eq62984
    | exact resolve eq62984 eq10342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10342 eq62984
  have eq63092 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) y) (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X0 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq63046 X0 X1
       have i₂ := eq3584 sF2 (M.op sF3 (M.op X0 X1)) y sF1
       grind)
    | (have i₁ := eq63046 X0 X1
       have i₂ := eq3584 sF1 (M.op sF3 (M.op X0 X1)) y sF2
       grind)
    | exact superpose eq3584 eq63046
    | exact resolve eq63046 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63046
  have eq63283 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op (M.op X0 x) (M.op X1 (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq4489 X0 X1 y
       have i₂ := eq25300 X0 X1
       grind)
    | exact superpose eq25300 eq4489
    | exact resolve eq4489 eq25300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65447 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X1 (M.op X0 X2)))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2237 X3 X1 (M.op X0 X2) X4
       have i₂ := eq4489 X0 X2 X1
       grind)
    | (have i₁ := eq2237 X3 X1 (M.op X0 X2) X4
       have i₂ := eq4489 X0 X1 X2
       grind)
    | exact superpose eq4489 eq2237
    | exact resolve eq2237 eq4489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4489
  have eq65521 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) (M.op (σ x) (σ y)))) = (M.op X2 (M.op (M.op X0 (σ x)) (M.op (σ y) X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq19753 eq2237
    | exact resolve eq2237 eq19753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19753
  have eq66015 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (σ x) (M.op (σ y) X1)))) = (M.op X2 (M.op (M.op X0 X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65521 X0 X1 X1
       have i₂ := eq2096 X0 X1 sF2 (M.op sF3 X1)
       grind)
    | exact superpose eq2096 eq65521
    | exact resolve eq65521 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65521
  have eq66086 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) = (M.op X3 (M.op X4 (M.op X1 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq65447 X1 X0 X2 X3 X4
       have i₂ := eq2096 X1 X4 X0 X2
       grind)
    | exact superpose eq2096 eq65447
    | exact resolve eq65447 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65447
  have eq66397 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (σ x) (M.op (σ y) X1)))) = (M.op X2 (M.op X0 (M.op X1 (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66015 X0 X2 X1
       have i₂ := eq2096 X0 X1 X2 sF4
       grind)
    | exact superpose eq2096 eq66015
    | exact resolve eq66015 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66015
  have eq67683 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 (M.op X1 X3))) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X4) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq3827 (M.op (M.op X0 X1) (M.op X2 X3)) X4 (M.op X2 (M.op X1 X3))
       have i₂ := eq2240 X2 X3 X0 X1
       grind)
    | exact superpose eq2240 eq3827
    | exact resolve eq3827 eq2240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2240 eq3827
  have eq67700 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 (M.op X1 X3))) = (M.op (M.op (M.op (M.op X0 X1) x) x) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq67683 X0 X1 X2 X3 x
       have i₂ := eq7402 (M.op X0 X1) (M.op X2 X3) x
       grind)
    | exact superpose eq7402 eq67683
    | exact resolve eq67683 eq7402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7402 eq67683
  have eq93435 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2693 X2 X3 X0 (M.op X3 X1)
       have i₂ := eq1147 X0 X1 X3
       grind)
    | exact superpose eq1147 eq2693
    | exact resolve eq2693 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93462 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op (M.op (M.op X0 X1) X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2693 X2 X3 (M.op (M.op X0 X1) X1) X3
       have i₂ := eq3723 X0 X1 X3
       grind)
    | exact superpose eq3723 eq2693
    | exact resolve eq2693 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2693
  have eq98538 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X2 X1)) x) (M.op X3 (M.op x y))) = (M.op (M.op (M.op X0 (M.op y X1)) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63283 (M.op X0 (M.op X2 X1)) X3
       have i₂ := eq2236 X2 X0 y X1
       grind)
    | (have i₁ := eq63283 (M.op X0 (M.op X2 X1)) X3
       have i₂ := eq2236 y X0 X2 X1
       grind)
    | exact superpose eq2236 eq63283
    | exact resolve eq63283 eq2236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq98608 : ∀ X0 X1 X2 : G, (M.op (M.op X2 y) (M.op X0 X1)) = (M.op (M.op X2 x) (M.op (M.op X0 x) (M.op y X1))) := by
    intro X0 X1 X2
    first
    | exact superpose eq46618 eq63283
    | exact resolve eq63283 eq46618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63283
  have eq98991 : ∀ X0 X1 X2 : G, (M.op (M.op X2 y) (M.op X0 X1)) = (M.op (M.op X2 x) (M.op X0 (M.op x (M.op y X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98608 X0 X1 X2
       have i₂ := eq2096 X0 (M.op X2 x) x (M.op y X1)
       grind)
    | exact superpose eq2096 eq98608
    | exact resolve eq98608 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98608
  have eq99048 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 x) (M.op X1 X2)) (M.op X3 (M.op x y))) = (M.op (M.op (M.op X0 (M.op y X1)) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq98538 X0 X1 X2 X3
       have i₂ := eq7935 X0 X2 X1 x
       grind)
    | exact superpose eq7935 eq98538
    | exact resolve eq98538 eq7935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7935 eq98538
  have eq99259 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) x) (M.op y (M.op x (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X0 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq63092 X0 X1
       have i₂ := eq98991 y (M.op sF1 (M.op sF2 (M.op sF3 (M.op X0 X1)))) sF1
       grind)
    | exact superpose eq98991 eq63092
    | exact resolve eq63092 eq98991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63092 eq98991
  have eq99319 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op y X1)) X2) X3) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99048 X0 X1 X2 X2
       have i₂ := eq93435 (M.op X0 x) (M.op X1 X2) X2 sF0
       grind)
    | (have i₁ := eq99048 X0 X1 X2 X3
       have i₂ := eq93435 (M.op X0 x) sF0 (M.op X1 X2) X3
       grind)
    | exact superpose eq93435 eq99048
    | exact resolve eq99048 eq93435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93435 eq99048
  have eq99464 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op y (M.op y (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X0 X1)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq99259 X0 X1
       have i₂ := eq3584 y (M.op y (M.op sF1 (M.op sF2 (M.op sF3 (M.op X0 X1))))) (M.op sF1 x) x
       grind)
    | (have i₁ := eq99259 X0 X1
       have i₂ := eq3584 x (M.op y (M.op sF1 (M.op sF2 (M.op sF3 (M.op X0 X1))))) (M.op sF1 x) y
       grind)
    | exact superpose eq3584 eq99259
    | exact resolve eq99259 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99259
  have eq99539 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 x) x) (M.op y (M.op (M.op X1 X2) X3))) = (M.op (M.op (M.op X0 (M.op y X1)) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq18698 eq99319
    | exact resolve eq99319 eq18698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99319
  have eq99626 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) X1) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X0 X1)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq99464 X0 X1
       have i₂ := eq1147 x (M.op sF1 (M.op sF2 (M.op sF3 (M.op X0 X1)))) y
       grind)
    | exact superpose eq1147 eq99464
    | exact resolve eq99464 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99464
  have eq99675 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 x) x) (M.op y (M.op X1 (M.op X2 X3)))) = (M.op (M.op (M.op X0 (M.op y X1)) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq99539 X0 X1 X2 X3
       have i₂ := eq2096 X1 y X2 X3
       grind)
    | exact superpose eq2096 eq99539
    | exact resolve eq99539 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99539
  have eq105310 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op X0 x) (M.op x y)) (M.op X3 (M.op X1 y))) X4) (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2264 (M.op X0 X1) (M.op X1 y) X3 X2 X4
       have i₂ := eq4558 X0 X1
       grind)
    | (have i₁ := eq2264 (M.op X0 x) (M.op x y) X2 X3 X4
       have i₂ := eq4558 X0 X1
       grind)
    | exact superpose eq4558 eq2264
    | exact resolve eq2264 eq4558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558
  have eq105410 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X3 (M.op X4 (M.op (M.op (M.op X0 X5) (M.op X2 X5)) X6))) = (M.op (M.op (M.op (M.op X3 (M.op X6 X1)) (M.op X0 (M.op X1 X2))) X7) (M.op X7 X4)) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq2264 X3 (M.op X6 X1) (M.op (M.op (M.op X0 X5) (M.op X2 X5)) X6) X4 X7
       have i₂ := eq2264 X0 X5 X2 X1 X6
       grind)
    | exact superpose eq2264 eq2264
    | exact resolve eq2264 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq106265 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op (M.op X3 (M.op X6 X1)) (M.op X0 (M.op X1 X2))) X7) (M.op X7 X4)) = (M.op X3 (M.op X4 (M.op (M.op X0 X5) (M.op (M.op X2 X5) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq105410 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq2096 (M.op X0 X5) X4 (M.op X2 X5) X6
       grind)
    | exact superpose eq2096 eq105410
    | exact resolve eq105410 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105410
  have eq106349 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op X0 x) x) (M.op y (M.op X3 (M.op X1 y)))) X4) (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq18698 eq105310
    | exact resolve eq105310 eq18698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18698 eq105310
  have eq106818 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op (M.op X3 (M.op X6 X1)) (M.op X0 (M.op X1 X2))) X7) (M.op X7 X4)) = (M.op X3 (M.op X4 (M.op X0 (M.op X5 (M.op (M.op X2 X5) X6))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq106265 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq2096 X0 X4 X5 (M.op (M.op X2 X5) X6)
       grind)
    | exact superpose eq2096 eq106265
    | exact resolve eq106265 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106265
  have eq106894 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op (M.op (M.op X0 x) x) x) x) (M.op y (M.op (M.op X3 (M.op X1 y)) (M.op X4 (M.op X4 X2))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq106349 X0 X1 X2 X3 X4
       have i₂ := eq99675 (M.op (M.op X0 x) x) (M.op X3 (M.op X1 y)) X4 (M.op X4 X2)
       grind)
    | exact superpose eq99675 eq106349
    | exact resolve eq106349 eq99675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99675 eq106349
  have eq107307 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op (M.op X3 (M.op X6 X1)) (M.op X0 (M.op X1 X2))) X7) (M.op X7 X4)) = (M.op X3 (M.op X4 (M.op X0 (M.op X5 (M.op X2 (M.op X5 X6)))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq106818 X0 X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq2096 X2 X5 X5 X6
       grind)
    | exact superpose eq2096 eq106818
    | exact resolve eq106818 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106818
  have eq107377 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 x) (M.op y (M.op x (M.op (M.op X3 (M.op X1 y)) (M.op X4 (M.op X4 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq106894 X0 X1 X2 X3 X4
       have i₂ := eq67700 (M.op X0 x) x y (M.op (M.op X3 (M.op X1 y)) (M.op X4 (M.op X4 X2)))
       grind)
    | exact superpose eq67700 eq106894
    | exact resolve eq106894 eq67700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67700 eq106894
  have eq107740 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op (M.op (M.op (M.op X3 (M.op X6 X1)) (M.op X0 (M.op X1 X2))) X7) (M.op X7 X4)) = (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq107307 X0 X1 X2 X3 X4 x X6 X7
       have i₂ := eq3851 X2 x X6 X0
       grind)
    | exact superpose eq3851 eq107307
    | exact resolve eq107307 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107307
  have eq107807 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 x) (M.op x (M.op y (M.op (M.op X3 (M.op X1 y)) (M.op X4 (M.op X4 X2)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq107377 X0 X1 X2 X3 X4
       have i₂ := eq3584 y (M.op (M.op X3 (M.op X1 y)) (M.op X4 (M.op X4 X2))) (M.op X0 x) x
       grind)
    | (have i₁ := eq107377 X0 X1 X2 X3 X4
       have i₂ := eq3584 x (M.op (M.op X3 (M.op X1 y)) (M.op X4 (M.op X4 X2))) (M.op X0 x) y
       grind)
    | exact superpose eq3584 eq107377
    | exact resolve eq107377 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107377
  have eq108158 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 x) (M.op x (M.op y (M.op X3 (M.op (M.op X1 y) (M.op X4 (M.op X4 X2))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq107807 X0 X1 X2 X3 X4
       have i₂ := eq2096 X3 y (M.op X1 y) (M.op X4 (M.op X4 X2))
       grind)
    | exact superpose eq2096 eq107807
    | exact resolve eq107807 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107807
  have eq108447 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 x) (M.op x (M.op y (M.op X3 (M.op X1 (M.op y (M.op X4 (M.op X4 X2)))))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq108158 X0 X1 X2 X3 X4
       have i₂ := eq2096 X1 X3 y (M.op X4 (M.op X4 X2))
       grind)
    | exact superpose eq2096 eq108158
    | exact resolve eq108158 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108158
  have eq108682 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 x) (M.op x (M.op y (M.op X3 (M.op X1 (M.op y X2)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq108447 X0 X1 X2 X3 x
       have i₂ := eq1147 y X2 x
       grind)
    | exact superpose eq1147 eq108447
    | exact resolve eq108447 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108447
  have eq110095 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op X0 x) x) X3) (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2365 X0 X1 X1 X3 X2
       have i₂ := eq3419 X0 X1
       grind)
    | (have i₁ := eq2365 X0 x x X3 x
       have i₂ := eq3419 X0 X1
       grind)
    | exact superpose eq3419 eq2365
    | exact resolve eq2365 eq3419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3419
  have eq110399 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op (M.op X0 X3) X1) X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq529 (M.op (M.op (M.op X0 X3) X1) X3) X3 X2
       have i₂ := eq2365 X0 X3 X1 X3 X2
       grind)
    | exact superpose eq2365 eq529
    | exact resolve eq529 eq2365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110428 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 (M.op X1 X2)) X5) (M.op (M.op X3 (M.op X2 X4)) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq424 (M.op (M.op (M.op X0 X3) X1) X4) (M.op X3 (M.op X2 X4)) X5
       have i₂ := eq2365 X0 X3 X1 X4 X2
       grind)
    | exact superpose eq2365 eq424
    | exact resolve eq424 eq2365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq110479 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 x) x) (M.op (M.op X1 X2) (M.op X3 (M.op X2 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq110428 X0 X1 X2 X3 X4 x
       have i₂ := eq61525 X0 (M.op X1 X2) x (M.op X3 (M.op X2 X4))
       grind)
    | exact superpose eq61525 eq110428
    | exact resolve eq110428 eq61525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61525 eq110428
  have eq110763 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq110095 X0 X1 X2 X3
       have i₂ := eq93462 X0 x X3 (M.op X1 (M.op X2 X3))
       grind)
    | exact superpose eq93462 eq110095
    | exact resolve eq110095 eq93462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93462 eq110095
  have eq110876 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op X2 (M.op X3 (M.op X2 X4))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq110479 X0 X1 X2 X3 X4
       have i₂ := eq2096 X1 (M.op (M.op X0 x) x) X2 (M.op X3 (M.op X2 X4))
       grind)
    | exact superpose eq2096 eq110479
    | exact resolve eq110479 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110479
  have eq111244 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X3) X1) X4) = (M.op (M.op (M.op X0 x) x) (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq110876 X0 X1 x X3 X4
       have i₂ := eq3851 X3 x X4 X1
       grind)
    | exact superpose eq3851 eq110876
    | exact resolve eq110876 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110876
  have eq111600 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op (M.op (M.op (M.op X3 x) x) (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X6 X1) X7))) (M.op X7 X4)) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq107740 X0 X1 X2 X3 X4 X6 X7
       have i₂ := eq111244 X3 (M.op X0 (M.op X1 X2)) (M.op X6 X1) X7
       grind)
    | exact superpose eq111244 eq107740
    | exact resolve eq107740 eq111244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107740
  have eq112036 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op (M.op (M.op (M.op X3 x) x) x) (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X6 X1) X7)) (M.op x (M.op X7 X4)))) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq111600 X0 X1 X2 X3 X4 X6 X7
       have i₂ := eq111244 (M.op X3 x) (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X6 X1) X7)) x (M.op X7 X4)
       grind)
    | exact superpose eq111244 eq111600
    | exact resolve eq111600 eq111244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111244 eq111600
  have eq112342 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op X3 (M.op x (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X6 X1) X7)) (M.op x (M.op X7 X4))))) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq112036 X0 X1 X2 X3 X4 X6 X7
       have i₂ := eq110399 X3 x (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X6 X1) X7)) (M.op x (M.op X7 X4))) x
       grind)
    | exact superpose eq110399 eq112036
    | exact resolve eq112036 eq110399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110399 eq112036
  have eq112705 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op X3 (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X6 X1) X7)) (M.op X7 X4))) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq112342 X0 X1 X2 X3 X4 X6 X7
       have i₂ := eq3851 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X6 X1) X7)) x (M.op X7 X4) X3
       grind)
    | exact superpose eq3851 eq112342
    | exact resolve eq112342 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112342
  have eq113007 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op X3 (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op (M.op X6 X1) X7) (M.op X7 X4)))) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq112705 X0 X1 X2 X3 X4 X6 X7
       have i₂ := eq2096 (M.op X0 (M.op X1 X2)) X3 (M.op (M.op X6 X1) X7) (M.op X7 X4)
       grind)
    | exact superpose eq2096 eq112705
    | exact resolve eq112705 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112705
  have eq113264 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) (M.op (M.op (M.op X6 X1) X7) (M.op X7 X4))))) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq113007 X0 X1 X2 X3 X4 X6 X7
       have i₂ := eq2096 X0 X3 (M.op X1 X2) (M.op (M.op (M.op X6 X1) X7) (M.op X7 X4))
       grind)
    | exact superpose eq2096 eq113007
    | exact resolve eq113007 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113007
  have eq113422 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op (M.op (M.op X6 X1) X7) (M.op X7 X4)))))) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq113264 X0 X1 X2 X3 X4 X6 X7
       have i₂ := eq2096 X1 X0 X2 (M.op (M.op (M.op X6 X1) X7) (M.op X7 X4))
       grind)
    | exact superpose eq2096 eq113264
    | exact resolve eq113264 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113264
  have eq113549 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X7 (M.op (M.op (M.op X6 X1) X7) X4)))))) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq113422 X0 X1 X2 X3 X4 X6 X7
       have i₂ := eq66086 (M.op (M.op X6 X1) X7) X7 X4 X1 X2
       grind)
    | (have i₁ := eq113422 X0 X1 X2 X3 X4 X6 X7
       have i₂ := eq66086 X7 (M.op (M.op X6 X1) X7) X4 X1 X2
       grind)
    | exact superpose eq66086 eq113422
    | exact resolve eq113422 eq66086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66086 eq113422
  have eq113645 : ∀ X0 X1 X2 X3 X4 X6 X7 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X7 (M.op (M.op X6 X1) (M.op X7 X4))))))) := by
    intro X0 X1 X2 X3 X4 X6 X7
    first
    | (have i₁ := eq113549 X0 X1 X2 X3 X4 X6 X7
       have i₂ := eq2096 (M.op X6 X1) X7 X7 X4
       grind)
    | exact superpose eq2096 eq113549
    | exact resolve eq113549 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113549
  have eq113729 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X6 X1) X4))))) := by
    intro X0 X1 X2 X3 X4 X6
    first
    | (have i₁ := eq113645 X0 X1 X2 X3 X4 X6 x
       have i₂ := eq3851 (M.op X6 X1) x X4 X2
       grind)
    | exact superpose eq3851 eq113645
    | exact resolve eq113645 eq3851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3851 eq113645
  have eq113792 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X2 X6)))) = (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X6 (M.op X1 X4)))))) := by
    intro X0 X1 X2 X3 X4 X6
    first
    | (have i₁ := eq113729 X0 X1 X2 X3 X4 X6
       have i₂ := eq2096 X6 X2 X1 X4
       grind)
    | exact superpose eq2096 eq113729
    | exact resolve eq113729 eq2096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096 eq113729
  have eq114254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq371
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq371
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq371 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq114284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq114254
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114254
    | exact resolve eq114254 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114254
  have eq114293 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq114284
    | exact resolve eq114284 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114284
  have eq114300 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq114293
       have r₂ := eq27
       grind)
    | exact resolve eq114293 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114293
  have eq114307 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq114300
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114300
    | exact resolve eq114300 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114300
  have eq114308 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq114307
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114307
    | exact resolve eq114307 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114307
  have eq114335 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op X0 (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq114308 eq2148
    | exact resolve eq2148 eq114308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114308
  have eq114371 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) X0)))) (M.op X0 (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq40468 eq114335
    | exact resolve eq114335 eq40468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40468 eq114335
  have eq114399 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op (σ (M.op x y)) (M.op (σ x) (M.op (σ y) (M.op X0 (M.op X0 (σ y)))))))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq99626 eq114371
    | exact resolve eq114371 eq99626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99626 eq114371
  have eq114419 : ∀ X0 : G, (σ y) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op (σ (M.op x y)) (M.op (σ x) (M.op X0 X0))))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq114399 x
       have i₂ := eq110763 sF2 x x sF3
       grind)
    | exact superpose eq110763 eq114399
    | exact resolve eq114399 eq110763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110763 eq114399
  have eq114435 : (σ y) = (M.op (M.op (σ (M.op x y)) x) (M.op x (M.op (σ (M.op x y)) (σ x)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq114419 x
       have i₂ := eq2112 sF2 sF1 x
       grind)
    | exact superpose eq2112 eq114419
    | exact resolve eq114419 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114419
  have eq114450 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39379 eq114435
    | exact resolve eq114435 eq39379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114435
  have eq114505 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) (M.op X0 y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2148 y y X0
       have i₂ := eq114450
       grind)
    | exact superpose eq114450 eq2148
    | exact resolve eq2148 eq114450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148 eq114450
  have eq114531 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2523 eq114505
    | exact resolve eq114505 eq2523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523 eq114505
  have eq114578 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq114531 eq1697
    | exact resolve eq1697 eq114531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq114585 : (τ (σ y)) = (M.op x (M.op x (τ (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq114531 eq39868
    | exact resolve eq39868 eq114531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39868 eq114531
  have eq114592 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq39 eq114585
    | exact resolve eq114585 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114585
  have eq114595 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq114578
    | (have j0 := eq114578 X0
       grind)
    | exact resolve eq114578 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114578
  have eq114596 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq114592
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq114592
    | exact resolve eq114592 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114592
  have eq119302 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op (M.op (σ x) (σ y)) (σ y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq114595 eq2112
    | exact resolve eq2112 eq114595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114595
  have eq119454 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op (σ y) (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq119302 X0 x
       have i₂ := eq2237 X0 sF4 sF3 x
       grind)
    | (have i₁ := eq119302 X0 x
       have i₂ := eq2237 X0 sF3 sF4 x
       grind)
    | exact superpose eq2237 eq119302
    | exact resolve eq119302 eq2237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2237 eq119302
  have eq119536 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (M.op (σ x) (M.op (σ y) (σ y))))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq66397 eq119454
    | exact resolve eq119454 eq66397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66397 eq119454
  have eq119597 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (σ x))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq119536 X0 X1
       have i₂ := eq2112 sF2 X1 sF3
       grind)
    | exact superpose eq2112 eq119536
    | exact resolve eq119536 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112 eq119536
  have eq190738 : ∀ X0 : G, (σ x) = (M.op (M.op (σ (M.op x y)) X0) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq119597 eq39379
    | exact resolve eq39379 eq119597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39379 eq119597
  have eq222210 : (τ (σ x)) = (M.op (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (τ (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq190738 eq237
    | exact resolve eq237 eq190738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190738
  have eq222405 : (τ (σ x)) = (M.op (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq222210
       have i₂ := eq237 sF1
       grind)
    | exact superpose eq237 eq222210
    | exact resolve eq222210 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq222210
  have eq222519 : (τ (σ x)) = (M.op (M.op (τ (σ (M.op x y))) x) (M.op x (M.op y (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (M.op y (τ (σ (M.op x y))))))))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq222405
       have i₂ := eq108682 (τ sF1) (τ sF1) (τ sF1) (τ sF1)
       grind)
    | exact superpose eq108682 eq222405
    | exact resolve eq222405 eq108682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108682 eq222405
  have eq222618 : (τ (σ x)) = (M.op (M.op (τ (σ (M.op x y))) x) (M.op (τ (σ (M.op x y))) (M.op x (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq222519
       have i₂ := eq113792 y x (τ sF1) (M.op (τ sF1) x) x (M.op (τ sF1) (M.op y (τ sF1)))
       grind)
    | (have i₁ := eq222519
       have i₂ := eq113792 x y (τ sF1) (M.op (τ sF1) x) (τ sF1) (τ sF1)
       grind)
    | exact superpose eq113792 eq222519
    | exact resolve eq222519 eq113792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113792 eq222519
  have eq222703 : (τ (σ x)) = (M.op (M.op (τ (σ (M.op x y))) x) (M.op x (M.op (τ (σ (M.op x y))) (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y))))))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq222618
       have i₂ := eq3584 (τ sF1) (M.op (τ sF1) (τ sF1)) (M.op (τ sF1) x) x
       grind)
    | (have i₁ := eq222618
       have i₂ := eq3584 x (M.op (τ sF1) (τ sF1)) (M.op (τ sF1) x) (τ sF1)
       grind)
    | exact superpose eq3584 eq222618
    | exact resolve eq222618 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3584 eq222618
  have eq222764 : (τ (σ x)) = (M.op (M.op (τ (σ (M.op x y))) x) (M.op x (τ (σ (M.op x y))))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq222703
       have i₂ := eq529 x (τ sF1) (τ sF1)
       grind)
    | exact superpose eq529 eq222703
    | exact resolve eq222703 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq222703
  have eq222812 : (τ (σ x)) = (M.op (M.op (M.op x y) x) (M.op x (M.op x y))) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq37 eq222764
    | exact resolve eq222764 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq222764
  have eq222849 : (τ (σ x)) = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq25300 eq222812
    | exact resolve eq222812 eq25300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25300 eq222812
  have eq222876 : x = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq38 eq222849
    | exact resolve eq222849 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222849
  have eq223010 : (M.op x (M.op x y)) = (M.op (M.op (M.op (M.op x y) x) x) (M.op y y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq222876 eq46618
    | exact resolve eq46618 eq222876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46618 eq222876
  have eq223035 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq223010
       have i₂ := eq3723 sF0 x y
       grind)
    | exact superpose eq3723 eq223010
    | exact resolve eq223010 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3723 eq223010
  have eq223276 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq223035 eq114596
    | exact resolve eq114596 eq223035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114596 eq223035
  have eq223358 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq223276
  have eq223416 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq223358 eq39
    | exact resolve eq39 eq223358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq223358
  have eq223462 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq38 eq223416
    | exact resolve eq223416 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq223416
  have eq223463 : y = (M.op x y) ∨ x = y := by grind
  clear eq223462
  have eq223468 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq223463 eq20
    | exact resolve eq20 eq223463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223474 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op y X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq223463 eq422
    | exact resolve eq422 eq223463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422 eq223463
  have eq223497 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq223468
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq223468
    | exact resolve eq223468 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223468
  have eq229860 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y X0)) (σ (M.op y X0))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq136 (M.op y X0)
       have i₂ := eq223474 X0
       grind)
    | exact superpose eq223474 eq136
    | exact resolve eq136 eq223474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223474
  have eq229997 : (σ x) = (M.op (M.op (σ y) x) (M.op x (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq229860 x
       have i₂ := eq15504 x
       grind)
    | exact superpose eq15504 eq229860
    | exact resolve eq229860 eq15504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15504 eq229860
  have eq230063 : (σ x) = (M.op (M.op (σ y) x) (M.op x (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq229997
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq229997
    | exact resolve eq229997 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229997
  have eq244931 : (σ y) = (M.op (σ x) (M.op x (M.op x (σ y)))) ∨ x = y := by
    first
    | exact superpose eq230063 eq424
    | exact resolve eq424 eq230063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424 eq230063
  have eq245055 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq244931
       have i₂ := eq1147 sF2 sF3 x
       grind)
    | exact superpose eq1147 eq244931
    | exact resolve eq244931 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147 eq244931
  have eq245103 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq245055
    | exact resolve eq245055 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245055
  have eq245228 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq245103 eq27
    | exact resolve eq27 eq245103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245103
  have eq245267 : x = y := by
    first
    | (have r₁ := eq245228
       have r₂ := eq223497
       grind)
    | exact resolve eq245228 eq223497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223497 eq245228
  have eq245271 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq245267
       grind)
    | exact superpose eq245267 eq18
    | exact resolve eq18 eq245267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq245272 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq245267
       grind)
    | exact superpose eq245267 eq24
    | exact resolve eq24 eq245267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq245267
  have eq254996 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq245272
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq245272
    | exact resolve eq245272 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245272
  have eq256851 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq254996 eq26
    | exact resolve eq26 eq254996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq254996
  have eq261620 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq136 x
       have i₂ := eq245271
       grind)
    | exact superpose eq245271 eq136
    | exact resolve eq136 eq245271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq245271
  have eq261775 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq261620
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq261620
    | exact resolve eq261620 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq261620
  have eq261821 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq256851 eq261775
    | exact resolve eq261775 eq256851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256851 eq261775
  have eq261846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq261821
    | exact resolve eq261821 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq261821
  have eq261857 : False := by grind
  exact eq261857

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_pyx_pxy_Equation2702 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq45 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq45
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq45 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq45
    | (have j0 := eq45 y
       grind)
    | exact resolve eq45 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq108 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq48 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq48
    | exact resolve eq48 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq16 X0 (M.op (M.op x X0) (M.op X0 x)) X3
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, x = (M.op (M.op (M.op X0 x) (M.op x y)) x) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 X0) (k X0 X1)) X0) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 (M.op (M.op X2 X0) (k X0 X1))
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : (M.op x y) = (k x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 x y
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF2 sF3
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq647 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq649 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq635
       grind)
    | exact superpose eq635 eq41
    | exact resolve eq41 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq649
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq649
    | exact resolve eq649 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq652 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq650
    | exact resolve eq650 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq652 eq642
    | exact resolve eq642 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq662
       have r₂ := eq27
       grind)
    | exact resolve eq662 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq685 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ (M.op x y) = (k y x) := by
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
  have eq687 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq669 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq669
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq669
       grind)
    | exact resolve eq12 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq669 eq177
    | exact resolve eq177 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq704
  have eq710 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq669 eq706
    | exact resolve eq706 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq706
  have eq712 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq652 eq709
    | exact resolve eq709 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq714 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq710
    | exact resolve eq710 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq718 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq714
       grind)
    | exact superpose eq714 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq714
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq714
       grind)
    | exact resolve eq12 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq714
       grind)
    | exact superpose eq714 eq177
    | exact resolve eq177 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq721 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq714
       grind)
    | exact superpose eq714 eq16
    | exact resolve eq16 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : x = (k x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq718
  have eq724 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq714 eq720
    | exact resolve eq720 eq714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq714 eq720
  have eq727 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq724
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq724
    | exact resolve eq724 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq731 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727 eq187
    | exact resolve eq187 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq731
    | exact resolve eq731 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq737 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727 eq735
    | exact resolve eq735 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq742 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq737 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq737
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq737
       grind)
    | exact resolve eq12 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq747 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq742
  have eq814 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq721 (M.op (M.op x y) x)
       have i₂ := eq721 x
       grind)
    | exact superpose eq721 eq721
    | exact resolve eq721 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq824 : y = (M.op (M.op y x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq814
  have eq832 : (M.op x y) = (M.op (M.op (M.op x y) x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq727 eq824
    | exact resolve eq824 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq846 : x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq832 eq178
    | exact resolve eq178 eq832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq854 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq846 eq832
    | exact resolve eq832 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832 eq846
  have eq864 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq854
  have eq978 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq712 eq181
    | exact resolve eq181 eq712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq986 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq978
    | exact resolve eq978 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq652 eq986
    | exact resolve eq986 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652 eq986
  have eq990 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq989
       have r₂ := eq27
       grind)
    | exact resolve eq989 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq996 : y = (M.op (M.op y x) y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq177 y x
       have i₂ := eq990
       grind)
    | exact superpose eq990 eq177
    | exact resolve eq177 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq990 eq996
    | exact resolve eq996 eq990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq990 eq996
  have eq1003 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1000
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1000
    | exact resolve eq1000 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq1004 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1003 eq29
    | exact resolve eq29 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1008 : (k y (M.op x y)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1003 eq117
    | exact resolve eq117 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq1011 : (k (M.op x y) y) = (τ (k (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1003 eq133
    | exact resolve eq133 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1003
  have eq1018 : (k x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq99 eq1011
    | exact resolve eq1011 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1011
  have eq1021 : (k y x) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115 eq1008
    | exact resolve eq1008 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq1008
  have eq1025 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq1004
    | exact resolve eq1004 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1029 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1025
       grind)
    | exact superpose eq1025 eq24
    | exact resolve eq24 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1034 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq685
       have i₂ := eq1025
       grind)
    | exact superpose eq1025 eq685
    | (have r₁ := eq685
       have r₂ := eq1025
       grind)
    | exact resolve eq685 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685
  have eq1039 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq1034
  have eq1042 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1029
    | exact resolve eq1029 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1128 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq635
       have i₂ := eq1018
       grind)
    | exact superpose eq1018 eq635
    | exact resolve eq635 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq1133 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1025 eq1128
    | exact resolve eq1128 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1190 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727 eq687
    | (have r₁ := eq687
       have r₂ := eq727
       grind)
    | exact resolve eq687 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq687
  have eq1191 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1190
  have eq1232 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) (k y (M.op x y))) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq613 y x X0
       have i₂ := eq1021
       grind)
    | exact superpose eq1021 eq613
    | (have j0 := eq613 y (M.op x y) X0
       grind)
    | exact resolve eq613 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq1257 : ∀ X0 : G, y = (M.op x y) ∨ y = (M.op (M.op (M.op X0 y) (k y (M.op x y))) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1232 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1232
    | (have j0 := eq1232 X0
       grind)
    | exact resolve eq1232 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1232
  have eq1258 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) (k y (M.op x y))) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1257 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1563 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq723
       grind)
    | exact superpose eq723 eq41
    | exact resolve eq41 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq723
  have eq1565 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1563
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1563
    | exact resolve eq1563 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq1567 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq727 eq1565
    | exact resolve eq1565 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq1589 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1191 eq142
    | exact resolve eq142 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1191
  have eq1592 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq1589
    | exact resolve eq1589 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589
  have eq1596 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1021 eq1592
    | exact resolve eq1592 eq1021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq1592
  have eq1603 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1567 eq642
    | exact resolve eq642 eq1567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1567
  have eq1621 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq747 eq153
    | exact resolve eq153 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq747
  have eq1623 : x = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq1621
    | exact resolve eq1621 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621
  have eq1626 : x = (k (M.op x y) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1018 eq1623
    | exact resolve eq1623 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018 eq1623
  have eq1629 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1025 eq1626
    | exact resolve eq1626 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq1654 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1596 eq181
    | exact resolve eq181 eq1596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1596
  have eq1665 : (σ x) = (k (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq737 eq1654
    | exact resolve eq1654 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737 eq1654
  have eq1706 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1039 eq40
    | exact resolve eq40 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1039
  have eq1708 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1706
    | exact resolve eq1706 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq1710 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1042 eq1708
    | exact resolve eq1708 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708
  have eq1725 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1629 eq181
    | exact resolve eq181 eq1629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1629
  have eq1736 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1725
    | exact resolve eq1725 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq1740 : (σ y) = (k (σ x) (σ y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq727 eq1736
    | exact resolve eq1736 eq727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727 eq1736
  have eq1773 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1665 eq108
    | exact resolve eq108 eq1665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq1665
  have eq1779 : x = (k y x) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq1773
    | exact resolve eq1773 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773
  have eq1783 : (M.op x y) = (k y (M.op x y)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1025 eq1779
    | exact resolve eq1779 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq2028 : (τ (σ y)) = (k x (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1740 eq91
    | exact resolve eq91 eq1740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1740
  have eq2037 : y = (k x y) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq2028
    | exact resolve eq2028 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2028
  have eq2043 : (M.op x y) = (k (M.op x y) y) ∨ y = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1025 eq2037
    | exact resolve eq2037 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025 eq2037
  have eq2774 : y = (M.op (M.op y (k y (M.op x y))) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1258 eq1258
    | exact resolve eq1258 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2781 : y = (M.op (M.op (M.op x y) (k y (M.op x y))) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1258 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1258
    | (have j0 := eq1258 x
       grind)
    | exact resolve eq1258 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq2798 : y = (M.op (M.op y (k y (M.op x y))) y) ∨ y = (M.op x y) := by grind
  clear eq2774
  have eq3064 : y = (M.op (M.op y (M.op x y)) y) ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1783 eq2798
    | exact resolve eq2798 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798
  have eq3083 : y = (M.op (M.op y (M.op x y)) y) ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) := by grind
  clear eq3064
  have eq3539 : y = (M.op (k y (M.op x y)) y) ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3083
       have i₂ := eq28 y sF0
       grind)
    | exact superpose eq28 eq3083
    | (have j1 := eq28 y (k y (M.op x y))
       grind)
    | exact resolve eq3083 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3083
  have eq3558 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1783 eq3539
    | exact resolve eq3539 eq1783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1783 eq3539
  have eq3559 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq3558
  have eq3563 : y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq3559 eq2781
    | exact resolve eq2781 eq3559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2781
  have eq3574 : y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq3563
  have eq3652 : y = (M.op (k (M.op x y) y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq3574
       have i₂ := eq28 sF0 y
       grind)
    | exact superpose eq28 eq3574
    | (have j1 := eq28 y (k (M.op x y) y)
       grind)
    | exact resolve eq3574 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3574
  have eq3671 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2043 eq3652
    | exact resolve eq3652 eq2043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043 eq3652
  have eq3672 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1133 eq3671
    | exact resolve eq3671 eq1133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133 eq3671
  have eq3673 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq3672
  have eq3683 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq3673 eq28
    | (have j0 := eq28 y (M.op x y)
       grind)
    | exact resolve eq28 eq3673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3673
  have eq3691 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq3683
  have eq3929 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3691 eq3559
    | exact resolve eq3559 eq3691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3559 eq3691
  have eq3939 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq3929
  have eq5740 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1603 eq177
    | exact resolve eq177 eq1603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5752 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1603 eq5740
    | exact resolve eq5740 eq1603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603 eq5740
  have eq5757 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5752
    | exact resolve eq5752 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5752
  have eq5758 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5757
  have eq5779 : (k x (M.op x y)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5758 eq181
    | exact resolve eq181 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5758
  have eq5798 : (M.op x y) = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq864 eq5779
    | exact resolve eq5779 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq5779
  have eq5807 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5798 eq36
    | exact resolve eq36 eq5798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq5798
  have eq5818 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5807
    | exact resolve eq5807 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5807
  have eq5820 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1042 eq5818
    | exact resolve eq5818 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5818
  have eq5920 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5820 eq642
    | exact resolve eq642 eq5820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq5820
  have eq5942 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5920
  have eq5964 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5942 eq177
    | exact resolve eq177 eq5942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq5976 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5942 eq5964
    | exact resolve eq5964 eq5942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5942 eq5964
  have eq5982 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq5976
    | exact resolve eq5976 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5976
  have eq5983 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5982
  have eq5984 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5983 eq27
    | exact resolve eq27 eq5983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5998 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5984
       have r₂ := eq1042
       grind)
    | exact resolve eq5984 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5984
  have eq6004 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5998 eq27
    | exact resolve eq27 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6005 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5998 eq176
    | exact resolve eq176 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq6006 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5998 eq179
    | exact resolve eq179 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq6007 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5998 eq187
    | exact resolve eq187 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq6016 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6007
       have i₂ := eq181 sF2
       grind)
    | exact superpose eq181 eq6007
    | exact resolve eq6007 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6007
  have eq6017 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1042 eq6004
    | exact resolve eq6004 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq6004
  have eq6020 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq6017
  have eq6027 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6016 eq142
    | exact resolve eq142 eq6016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq6016
  have eq6032 : x = (k (τ (M.op (σ x) (σ x))) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq6027
    | exact resolve eq6027 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6027
  have eq6359 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (k (σ y) X0)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6005 x
       have i₂ := eq28 sF3 x
       grind)
    | exact superpose eq28 eq6005
    | (have j1 := eq28 (σ y) (M.op (σ x) (k (σ y) X0))
       grind)
    | exact resolve eq6005 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6005
  have eq6416 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6006 eq6006
    | exact resolve eq6006 eq6006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6006
  have eq6441 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq6416
  have eq6470 : x = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6441 eq6032
    | exact resolve eq6032 eq6441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6032 eq6441
  have eq6494 : x = (k (τ (σ x)) x) ∨ x = (M.op x y) := by grind
  clear eq6470
  have eq6499 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq6494
    | exact resolve eq6494 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq6494
  have eq6531 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq647 x
       have i₂ := eq6499
       grind)
    | exact superpose eq6499 eq647
    | (have j0 := eq647 x
       grind)
    | (have r₁ := eq647 x
       have r₂ := eq6499
       grind)
    | exact resolve eq647 eq6499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6499
  have eq6534 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq6531
  have eq14315 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1710 eq6359
    | (have j0 := eq6359 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq6359 eq1710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1710 eq6359
  have eq14362 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq14315
  have eq14370 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq14362
    | exact resolve eq14362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14362
  have eq14375 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq14370
    | exact resolve eq14370 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14370
  have eq14378 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq5983 eq14375
    | exact resolve eq14375 eq5983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5983 eq14375
  have eq14379 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq14378
    | exact resolve eq14378 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14378
  have eq14380 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq14379
  have eq14381 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq5998 eq14380
    | exact resolve eq14380 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5998 eq14380
  have eq14382 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14381
       have r₂ := eq6020
       grind)
    | exact resolve eq14381 eq6020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6020 eq14381
  have eq14386 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6534
       have i₂ := eq14382
       grind)
    | exact superpose eq14382 eq6534
    | exact resolve eq6534 eq14382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6534 eq14382
  have eq14419 : x = (M.op x y) := by grind
  clear eq14386
  have eq14425 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14419
       grind)
    | exact superpose eq14419 eq18
    | exact resolve eq18 eq14419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14426 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq14419
       grind)
    | exact superpose eq14419 eq22
    | exact resolve eq22 eq14419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq14419
  have eq14501 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14426 eq20
    | exact resolve eq20 eq14426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14629 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq14425
       have i₂ := eq28 sF0 y
       grind)
    | exact superpose eq28 eq14425
    | (have j1 := eq28 (M.op x y) y
       grind)
    | exact resolve eq14425 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14632 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14425 eq3939
    | exact resolve eq3939 eq14425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3939 eq14425
  have eq14676 : y = (M.op x y) := by grind
  clear eq14632
  have eq14691 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq14629
       have i₂ := eq14676
       grind)
    | exact superpose eq14676 eq14629
    | exact resolve eq14629 eq14676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14629
  have eq14693 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq14691
       have i₂ := eq14676
       grind)
    | exact superpose eq14676 eq14691
    | exact resolve eq14691 eq14676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14691
  have eq14694 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq647 (M.op x y)
       grind)
    | (have r₁ := eq14693
       have r₂ := eq647 (M.op x y)
       grind)
    | exact resolve eq14693 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647 eq14693
  have eq14696 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq14676
       grind)
    | exact superpose eq14676 eq24
    | exact resolve eq24 eq14676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq14676
  have eq14728 : (σ x) = (σ y) := by
    first
    | exact superpose eq14426 eq14696
    | exact resolve eq14696 eq14426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14426 eq14696
  have eq14736 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq14728 eq26
    | exact resolve eq26 eq14728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq14728
  have eq14971 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq14694 eq181
    | exact resolve eq181 eq14694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq14990 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq14694 eq14971
    | exact resolve eq14971 eq14694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14694 eq14971
  have eq15005 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq14990 eq38
    | exact resolve eq38 eq14990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq14990
  have eq15023 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15005
    | exact resolve eq15005 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15005
  have eq15026 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq14501 eq15023
    | exact resolve eq15023 eq14501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15023
  have eq15070 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14736 eq28
    | exact resolve eq28 eq14736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq14736
  have eq15082 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15026 eq15070
    | exact resolve eq15070 eq15026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15026 eq15070
  have eq15083 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15082
  have eq15100 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq15083 eq27
    | exact resolve eq27 eq15083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15083
  have eq15118 : False := by grind
  exact eq15118

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
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
  have eq76 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq76
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq76
    | (have j1 := eq70 x x
       grind)
    | exact resolve eq76 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq91
    | exact resolve eq91 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq97
    | exact resolve eq97 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq420 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq428 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq420 X0
       grind)
    | exact superpose eq420 eq13
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq420 X0
       grind)
    | exact resolve eq13 eq420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq435 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq428 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq98 eq70
    | (have j0 := eq70 x (σ x)
       grind)
    | exact resolve eq70 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq823
    | exact resolve eq823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq827 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq824
       have r₂ := eq27
       grind)
    | exact resolve eq824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq844 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq827 eq435
    | exact resolve eq435 eq827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq865 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq844 eq49
    | exact resolve eq49 eq844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq844
  have eq869 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq865
    | exact resolve eq865 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq865
  have eq872 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70 x x
       have i₂ := eq869
       grind)
    | exact superpose eq869 eq70
    | (have j0 := eq70 x x
       grind)
    | exact resolve eq70 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq873 : x = (M.op x x) := by grind
  clear eq872
  have eq895 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq53
    | exact resolve eq53 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq896 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq50
    | exact resolve eq50 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq898 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq14
    | exact resolve eq14 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq899 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq14
    | exact resolve eq14 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq908 : x = (k x x) := by
    first
    | (have i₁ := eq435 x
       have i₂ := eq873
       grind)
    | exact superpose eq873 eq435
    | exact resolve eq435 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435 eq873
  have eq914 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq908
       grind)
    | exact superpose eq908 eq43
    | exact resolve eq43 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq908
  have eq918 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq914
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq914
    | exact resolve eq914 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq914
  have eq937 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq918 eq70
    | (have j0 := eq70 x (σ x)
       grind)
    | exact resolve eq70 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq918
  have eq938 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq937
  have eq945 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq938 eq51
    | exact resolve eq51 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq938
  have eq1100 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq899 (M.op x X0)
       have i₂ := eq898 X0
       grind)
    | exact superpose eq898 eq899
    | exact resolve eq899 eq898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1104 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq895 eq899
    | exact resolve eq899 eq895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1118 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1104 eq895
    | exact resolve eq895 eq1104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq895 eq1104
  have eq1159 : y = (M.op x y) := by
    first
    | exact superpose eq1118 eq896
    | exact resolve eq896 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896 eq1118
  have eq1173 : y = (M.op x y) := by
    first
    | (have i₁ := eq1159
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1159
    | exact resolve eq1159 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1159
  have eq1174 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1173 eq20
    | exact resolve eq20 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1173
  have eq1214 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1174
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1174
    | exact resolve eq1174 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1174
  have eq1216 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1214 eq26
    | exact resolve eq26 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1235 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1214 eq945
    | exact resolve eq945 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq1214
  have eq1518 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq898 X0
       have i₂ := eq1100 X0
       grind)
    | exact superpose eq1100 eq898
    | exact resolve eq898 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898 eq1100
  have eq1734 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq899 X0
       have i₂ := eq1518 X0
       grind)
    | exact superpose eq1518 eq899
    | exact resolve eq899 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899 eq1518
  have eq1797 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 x X0
       have i₂ := eq1734 X0
       grind)
    | exact superpose eq1734 eq14
    | exact resolve eq14 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1827 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1797 X0 X1
       have i₂ := eq1734 X1
       grind)
    | exact superpose eq1734 eq1797
    | exact resolve eq1797 eq1734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734 eq1797
  have eq2216 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq1827
    | (have j0 := eq1827 (σ y) (σ x)
       grind)
    | exact resolve eq1827 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1827
  have eq2278 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2216 eq1235
    | exact resolve eq1235 eq2216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235 eq2216
  have eq2298 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1216 eq2278
    | exact resolve eq2278 eq1216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216 eq2278
  have eq2300 : False := by grind
  exact eq2300

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq55 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq78 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq81 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq78 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq86 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq16
    | exact resolve eq16 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq37 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq116
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq38
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq38 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq159 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq520 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq524 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq530 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq520 X0
       grind)
    | exact superpose eq520 eq14
    | exact resolve eq14 eq520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq81 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq816 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq54 eq530
    | exact resolve eq530 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq818 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq55 eq530
    | exact resolve eq530 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq530
  have eq2387 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq524 X0
       have j1 := eq674 X0
       grind)
    | (have r₁ := eq524 X0
       have r₂ := eq674 X0
       grind)
    | exact resolve eq524 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524 eq674
  have eq6770 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq99 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq99
    | (have j0 := eq99 y
       grind)
    | exact resolve eq99 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq6792 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6770
  have eq6795 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6792
       have i₂ := eq76
       grind)
    | exact superpose eq76 eq6792
    | exact resolve eq6792 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq6792
  have eq6819 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6795
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6795 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6795
  have eq6846 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6819 eq91
    | exact resolve eq91 eq6819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq6819
  have eq6983 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq137
    | (have j0 := eq137 (M.op x y)
       grind)
    | exact resolve eq137 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq7004 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6983
  have eq7006 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq7004
    | exact resolve eq7004 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq7004
  have eq7037 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq7006
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq7006 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7006
  have eq7083 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq7037 eq159
    | exact resolve eq159 eq7037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq7037
  have eq10272 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10272
    | exact resolve eq10272 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10272
  have eq10284 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq10273
       have r₂ := eq28
       grind)
    | exact resolve eq10273 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10273
  have eq10286 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq10284
    | exact resolve eq10284 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10284
  have eq10494 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10286 eq520
    | exact resolve eq520 eq10286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10498 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10286 eq2387
    | exact resolve eq2387 eq10286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10286
  have eq10527 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq10494
    | exact resolve eq10494 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10494
  have eq10545 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2387 y
       have i₂ := eq10527
       grind)
    | exact superpose eq10527 eq2387
    | exact resolve eq2387 eq10527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10527
  have eq10816 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq10545
       grind)
    | exact superpose eq10545 eq75
    | exact resolve eq75 eq10545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq10545
  have eq10830 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10816
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10816
    | exact resolve eq10816 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10816
  have eq11097 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10830 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq10830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10830
  have eq11100 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11097
    | exact resolve eq11097 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11097
  have eq11101 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11100
  have eq11113 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11101
    | exact resolve eq11101 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11101
  have eq11114 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11113
  have eq11341 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11114 eq520
    | exact resolve eq520 eq11114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11114
  have eq11380 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq11341
    | exact resolve eq11341 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11341
  have eq11381 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11380
  have eq11388 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11381 eq28
    | exact resolve eq28 eq11381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11381
  have eq12410 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq10498 eq117
    | exact resolve eq117 eq10498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq10498
  have eq12419 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12410
  have eq12427 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12419
       have r₂ := eq11388
       grind)
    | exact resolve eq12419 eq11388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12419
  have eq12436 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq520 y
       have i₂ := eq12427
       grind)
    | exact superpose eq12427 eq520
    | exact resolve eq520 eq12427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12427
  have eq12476 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12436
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12436
    | exact resolve eq12436 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12436
  have eq12485 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12476 eq67
    | (have r₁ := eq67
       have r₂ := eq12476
       grind)
    | exact resolve eq67 eq12476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq12486 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12476 eq220
    | exact resolve eq220 eq12476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12509 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12476 eq818
    | exact resolve eq818 eq12476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12513 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12485
  have eq12984 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12509 eq12486
    | exact resolve eq12486 eq12509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12509
  have eq13026 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12984
  have eq13028 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq13026
    | exact resolve eq13026 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13026
  have eq13061 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13028 eq12476
    | exact resolve eq12476 eq13028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12476
  have eq13066 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq13061
  have eq13070 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13066 eq27
    | exact resolve eq27 eq13066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13066
  have eq14324 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13070 eq12486
    | exact resolve eq12486 eq13070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12486 eq13070
  have eq14392 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq14324
  have eq14445 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13028 eq14392
    | exact resolve eq14392 eq13028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13028 eq14392
  have eq14496 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq14445
  have eq14625 : (τ (σ y)) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14496 eq6846
    | exact resolve eq6846 eq14496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14496
  have eq14714 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq14625
    | exact resolve eq14625 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14625
  have eq15535 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12513 eq86
    | exact resolve eq86 eq12513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq12513
  have eq15566 : (k y x) = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6846 eq15535
    | exact resolve eq15535 eq6846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6846 eq15535
  have eq15849 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14714
       have i₂ := eq15566
       grind)
    | exact superpose eq15566 eq14714
    | exact resolve eq14714 eq15566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14714 eq15566
  have eq15857 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15849
  have eq15897 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq15857
       grind)
    | exact superpose eq15857 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq15857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15857
  have eq15898 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15897
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15897
    | exact resolve eq15897 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15897
  have eq15899 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15898
  have eq15911 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15899
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15899
    | exact resolve eq15899 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15899
  have eq15912 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15911
  have eq15972 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq520 y
       have i₂ := eq15912
       grind)
    | exact superpose eq15912 eq520
    | exact resolve eq520 eq15912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520 eq15912
  have eq16015 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15972
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15972
    | exact resolve eq15972 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15972
  have eq16016 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq16015
  have eq16017 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16016 eq21
    | exact resolve eq21 eq16016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16016
  have eq16158 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16017
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16017
    | exact resolve eq16017 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16017
  have eq16296 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16158 eq11388
    | (have r₁ := eq11388
       have r₂ := eq16158
       grind)
    | exact resolve eq11388 eq16158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11388
  have eq16336 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16296
  have eq16337 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16336
  have eq16426 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16337 eq220
    | exact resolve eq220 eq16337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq16449 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16337 eq818
    | exact resolve eq818 eq16337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818 eq16337
  have eq29270 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16449 eq16426
    | exact resolve eq16426 eq16449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16426 eq16449
  have eq29332 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq29270
  have eq29336 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq29332
    | exact resolve eq29332 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29332
  have eq29341 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29336 eq28
    | exact resolve eq28 eq29336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29336
  have eq29422 : x = (M.op x y) := by
    first
    | (have r₁ := eq29341
       have r₂ := eq16158
       grind)
    | exact resolve eq29341 eq16158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16158 eq29341
  have eq29739 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq29422 eq21
    | exact resolve eq21 eq29422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq29816 : x = (M.op x x) := by
    first
    | exact superpose eq29422 eq816
    | exact resolve eq816 eq29422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq29891 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq29739
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29739
    | exact resolve eq29739 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29739
  have eq29943 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq29891 eq27
    | exact resolve eq27 eq29891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq30718 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq51 x
       have i₂ := eq29816
       grind)
    | exact superpose eq29816 eq51
    | exact resolve eq51 eq29816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq30747 : x = (k x x) := by
    first
    | (have i₁ := eq2387 x
       have i₂ := eq29816
       grind)
    | exact superpose eq29816 eq2387
    | exact resolve eq2387 eq29816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2387
  have eq30842 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq29422 eq30718
    | exact resolve eq30718 eq29422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30718
  have eq30869 : y = (M.op x y) := by
    first
    | (have i₁ := eq30842
       have i₂ := eq29816
       grind)
    | exact superpose eq29816 eq30842
    | exact resolve eq30842 eq29816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29816 eq30842
  have eq30879 : y = (M.op x y) := by
    first
    | (have i₁ := eq30869
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq30869
    | exact resolve eq30869 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq30869
  have eq30886 : x = y := by
    first
    | exact superpose eq29422 eq30879
    | exact resolve eq30879 eq29422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30879
  have eq30890 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq30886
       grind)
    | exact superpose eq30886 eq25
    | exact resolve eq25 eq30886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq30886
  have eq31064 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq30890
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30890
    | exact resolve eq30890 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30890
  have eq31128 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29891 eq31064
    | exact resolve eq31064 eq29891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31064
  have eq31522 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq31128 eq29943
    | exact resolve eq29943 eq31128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29943 eq31128
  have eq31705 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31522 eq7083
    | exact resolve eq7083 eq31522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7083 eq31522
  have eq31776 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq29422 eq31705
    | exact resolve eq31705 eq29422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29422 eq31705
  have eq31782 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq31776
       have i₂ := eq30747
       grind)
    | exact superpose eq30747 eq31776
    | exact resolve eq31776 eq30747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30747 eq31776
  have eq31800 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31782 eq15
    | exact resolve eq15 eq31782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31782
  have eq31854 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31800
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31800
    | exact resolve eq31800 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq31800
  have eq31871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29891 eq31854
    | exact resolve eq31854 eq29891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29891 eq31854
  have eq31878 : False := by grind
  exact eq31878

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq89 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq89
    | exact resolve eq89 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq95
    | exact resolve eq95 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq97 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq112 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq112 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq112 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq112 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq116 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq43
    | exact resolve eq43 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq118 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq49
    | exact resolve eq49 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq119 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq118
       have i₂ := eq113 x
       grind)
    | exact superpose eq113 eq118
    | exact resolve eq118 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq121 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq113 sF2
       grind)
    | exact superpose eq113 eq116
    | exact resolve eq116 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq113 sF1
       grind)
    | exact superpose eq113 eq140
    | exact resolve eq140 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq146 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq143
       have i₂ := eq113 sF0
       grind)
    | exact superpose eq113 eq143
    | exact resolve eq143 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq143
  have eq168 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq146 eq16
    | exact resolve eq16 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146
  have eq255 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq266 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq530 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
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
  have eq541 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq530 X0
       grind)
    | exact superpose eq530 eq14
    | exact resolve eq14 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq1454 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq541
    | exact resolve eq541 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1457 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq541
    | exact resolve eq541 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq541
  have eq11464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11465 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11464
    | exact resolve eq11464 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11464
  have eq11476 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11465
       have r₂ := eq27
       grind)
    | exact resolve eq11465 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11465
  have eq11480 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11476
    | exact resolve eq11476 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11476
  have eq11482 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11480
    | exact resolve eq11480 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11480
  have eq11485 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11482 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11482
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11482
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11482
       grind)
    | exact resolve eq12 eq11482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11482
  have eq11524 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11485
       have r₂ := eq26
       grind)
    | exact resolve eq11485 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11485
  have eq11526 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11524
    | exact resolve eq11524 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11524
  have eq11527 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq11526
  have eq11617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11527 eq98
    | exact resolve eq98 eq11527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq11527
  have eq11625 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11617
  have eq11627 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11625
       have r₂ := eq27
       grind)
    | exact resolve eq11625 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11625
  have eq11630 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11627
       grind)
    | exact superpose eq11627 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11627
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq11627
       grind)
    | exact resolve eq12 eq11627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11627
  have eq11669 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11630
       have r₂ := eq18
       grind)
    | exact resolve eq11630 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11630
  have eq11671 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11669
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11669
    | exact resolve eq11669 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11669
  have eq11672 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11671
  have eq11898 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11672
       grind)
    | exact superpose eq11672 eq74
    | exact resolve eq74 eq11672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq11672
  have eq11912 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11898
    | exact resolve eq11898 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11898
  have eq11978 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11912 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11981 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11978
    | exact resolve eq11978 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11978
  have eq11992 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11981
       have r₂ := eq27
       grind)
    | exact resolve eq11981 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11981
  have eq11996 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11992
    | exact resolve eq11992 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11992
  have eq11998 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11996
    | exact resolve eq11996 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11996
  have eq11999 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11998
  have eq12003 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11999 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11999
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq11999
       grind)
    | exact resolve eq12 eq11999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11999
  have eq12042 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12003
       have r₂ := eq26
       grind)
    | exact resolve eq12003 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12003
  have eq12044 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12042
    | exact resolve eq12042 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12042
  have eq12045 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12044
  have eq12156 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12045 eq11912
    | exact resolve eq11912 eq12045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11912 eq12045
  have eq12158 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12156
  have eq12162 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12158
       have r₂ := eq27
       grind)
    | exact resolve eq12158 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12158
  have eq12168 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12162 eq266
    | exact resolve eq266 eq12162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq12192 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12162 eq1457
    | exact resolve eq1457 eq12162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1457
  have eq12220 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12192 eq119
    | exact resolve eq119 eq12192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq12331 : x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq12220
    | exact resolve eq12220 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12220
  have eq12583 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12192 eq12168
    | exact resolve eq12168 eq12192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12168 eq12192
  have eq12625 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12583
  have eq12628 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12625
    | exact resolve eq12625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12625
  have eq12667 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12628 eq12162
    | exact resolve eq12162 eq12628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12162 eq12628
  have eq12672 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq12667
  have eq12694 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12672 eq29
    | exact resolve eq29 eq12672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12672
  have eq12839 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28 eq12694
    | exact resolve eq12694 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq12694
  have eq12854 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq12839 eq20
    | exact resolve eq20 eq12839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12935 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq12839 eq1454
    | exact resolve eq1454 eq12839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq13007 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq12854
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12854
    | exact resolve eq12854 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12854
  have eq13625 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq121
       have i₂ := eq12935
       grind)
    | exact superpose eq12935 eq121
    | exact resolve eq121 eq12935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq12935
  have eq13739 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq13625
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13625
    | exact resolve eq13625 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13625
  have eq14162 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq13007 eq13739
    | exact resolve eq13739 eq13007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13007 eq13739
  have eq14242 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq14162
  have eq14706 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14242 eq168
    | exact resolve eq168 eq14242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14242
  have eq14795 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq14706
    | exact resolve eq14706 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14706
  have eq15009 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq14795 eq255
    | exact resolve eq255 eq14795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq14795
  have eq15162 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq12839 eq15009
    | exact resolve eq15009 eq12839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15009
  have eq15210 : y = (M.op x y) ∨ x = y := by grind
  clear eq15162
  have eq15212 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq15210
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15210
    | exact resolve eq15210 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15210
  have eq15321 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq15212 eq12839
    | exact resolve eq12839 eq15212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12839 eq15212
  have eq15330 : x = y := by grind
  clear eq15321
  have eq15403 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15330
       grind)
    | exact superpose eq15330 eq18
    | exact resolve eq18 eq15330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq15404 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq15330
       grind)
    | exact superpose eq15330 eq24
    | exact resolve eq24 eq15330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15330
  have eq15538 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15404
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15404
    | exact resolve eq15404 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15404
  have eq15555 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15538 eq26
    | exact resolve eq26 eq15538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15538
  have eq15747 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12331
       have i₂ := eq15403
       grind)
    | exact superpose eq15403 eq12331
    | exact resolve eq12331 eq15403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12331
  have eq15824 : x = (M.op x y) := by grind
  clear eq15747
  have eq15863 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq15824 eq20
    | exact resolve eq20 eq15824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq16035 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15863
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15863
    | exact resolve eq15863 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15863
  have eq16454 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16035 eq15555
    | exact resolve eq15555 eq16035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15555
  have eq16464 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq16454 eq168
    | exact resolve eq168 eq16454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq16454
  have eq16538 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15824 eq16464
    | exact resolve eq16464 eq15824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16464
  have eq16550 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16538
       have i₂ := eq15403
       grind)
    | exact superpose eq15403 eq16538
    | exact resolve eq16538 eq15403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15403 eq16538
  have eq16557 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq15824 eq16550
    | exact resolve eq16550 eq15824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15824 eq16550
  have eq16586 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16557 eq15
    | exact resolve eq15 eq16557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16557
  have eq16643 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16586
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16586
    | exact resolve eq16586 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq16586
  have eq16661 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16035 eq16643
    | exact resolve eq16643 eq16035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16035 eq16643
  have eq16676 : False := by grind
  exact eq16676

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq66 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4)) X5)) X0) = X0 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq19 X0 (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X4 X5
       have i₂ := eq19 X0 X1 X2 X3
       grind)
    | exact superpose eq19 eq19
    | exact resolve eq19 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq19
    | exact resolve eq19 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X1 (M.op X0 X0) X0 X2
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq19
    | exact resolve eq19 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq79 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq9
    | exact resolve eq9 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq94 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq79
    | exact resolve eq79 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4)) X5) X0) X5) = X5 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq20 X0 (M.op (M.op (M.op (M.op X1 X2) (M.op X1 X3)) X0) X2) X4 X5
       have i₂ := eq20 X2 X1 X3 X0
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq326 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq441 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq75 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq75
    | exact resolve eq75 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq635 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq326 y x
       grind)
    | exact superpose eq326 eq16
    | (have j1 := eq326 y x
       grind)
    | exact resolve eq16 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq637 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X1) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X1) (σ X0)
       have i₂ := eq326 X0 X1
       grind)
    | exact superpose eq326 eq9
    | (have j1 := eq326 X0 X1
       grind)
    | exact resolve eq9 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq638 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq326 X0 X1
       grind)
    | exact superpose eq326 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq326 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq326 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq326 X0 X1
       grind)
    | exact resolve eq12 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq326 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq326 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq663 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq661 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq675 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq638 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq638 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq638 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq638 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq679 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq675
    | (have j0 := eq675 X0 X1
       grind)
    | exact resolve eq675 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq684 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq663 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq663
    | (have j0 := eq663 (τ X0)
       grind)
    | exact resolve eq663 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq663
  have eq686 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq684 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq684
    | (have j0 := eq684 X0
       grind)
    | exact resolve eq684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq689 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq686 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq686
    | (have j0 := eq686 X0
       grind)
    | exact resolve eq686 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq3177 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 : G, (M.op (M.op (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X5)) X6)) X7)) X1) X0) X8)) X9) X1) X9) = X9 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8 X9
    first
    | (have i₁ := eq219 X1 (M.op X0 (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op (M.op X2 X0) (M.op X2 X3)) X4)) X5)) X6)) X0 X7 X8 X9
       have i₂ := eq66 X0 X2 X3 X4 X5 X6
       grind)
    | exact superpose eq66 eq219
    | exact resolve eq219 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq219
  have eq5399 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq662 (τ X1) (τ X0)
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq662
    | (have j0 := eq662 (τ X1) (τ X0)
       grind)
    | exact resolve eq662 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq5415 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5399 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5399
    | (have j0 := eq5399 X0 X1
       grind)
    | exact resolve eq5399 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5399
  have eq5422 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5415 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5415
    | (have j0 := eq5415 X0 X1
       grind)
    | exact resolve eq5415 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5415
  have eq5428 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5422 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5422
    | (have j0 := eq5422 X0 X1
       grind)
    | exact resolve eq5422 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5422
  have eq5433 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq5428 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5428
    | (have j0 := eq5428 X0 X1
       grind)
    | exact resolve eq5428 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5428
  have eq5438 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5433 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5433
    | (have j0 := eq5433 X0 X1
       grind)
    | exact resolve eq5433 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5433
  have eq5443 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5438 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5438
    | (have j0 := eq5438 X0 X1
       grind)
    | exact resolve eq5438 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5438
  have eq5508 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq635
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq635
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq635 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq5511 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq5508
  have eq5953 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X1)) X2) (σ (τ (k X0 X1)))) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq637 (τ X0) (τ X1) X2
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq637
    | (have j0 := eq637 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq637 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq637
  have eq6050 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X1)) X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5953 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq5953
    | (have j0 := eq5953 X0 X1 X2
       grind)
    | exact resolve eq5953 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953
  have eq6058 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6050 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6050
    | (have j0 := eq6050 X0 X1 X2
       grind)
    | exact resolve eq6050 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6050
  have eq6064 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (τ X0)) X1) ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6058 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq6058
    | (have j0 := eq6058 X0 X1 X2
       grind)
    | exact resolve eq6058 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6058
  have eq6069 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X0 ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6064 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6064
    | (have j0 := eq6064 X0 X1 X2
       grind)
    | exact resolve eq6064 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6064
  have eq6074 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = X0 ∨ (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6069 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6069
    | (have j0 := eq6069 X0 X1 X2
       grind)
    | exact resolve eq6069 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6069
  have eq6079 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (k X0 X1)) X2) = X2 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6074 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6074
    | (have j0 := eq6074 X0 X1 X2
       grind)
    | exact resolve eq6074 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6074
  have eq35731 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 (k X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 (k X1 X0)
       have i₂ := eq6079 X1 X0 X0
       grind)
    | exact superpose eq6079 eq79
    | (have j1 := eq6079 X1 X0 x
       grind)
    | exact resolve eq79 eq6079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6079
  have eq38891 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq5511
       grind)
    | exact superpose eq5511 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq5511
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq5511
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5511
       grind)
    | exact resolve eq13 eq5511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5511
  have eq38992 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq38891
  have eq38993 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq38992
  have eq39037 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq38993
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq38993
    | exact resolve eq38993 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38993
  have eq746440 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94 (σ x) (σ y)
       have i₂ := eq39037
       grind)
    | exact superpose eq39037 eq94
    | exact resolve eq94 eq39037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39037
  have eq776369 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq746440
       grind)
    | exact superpose eq746440 eq12
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq746440
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq746440
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq746440
       grind)
    | exact resolve eq12 eq746440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746440
  have eq776794 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq776369
  have eq776967 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq776794
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq776794
    | exact resolve eq776794 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776794
  have eq777293 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq776967
       grind)
    | exact superpose eq776967 eq10
    | exact resolve eq10 eq776967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776967
  have eq777510 : x = (k y x) ∨ (σ x) = (σ (k x x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq777293
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq777293
    | exact resolve eq777293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777293
  have eq777511 : (σ x) = (σ (k x x)) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq777510
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq777510
       have r₂ := eq13 x y
       grind)
    | exact resolve eq777510 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777510
  have eq777554 : (τ (σ x)) = (k x x) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq777511
       grind)
    | exact superpose eq777511 eq10
    | exact resolve eq10 eq777511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777511
  have eq777767 : x = (k y x) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq777554
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq777554
    | exact resolve eq777554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777554
  have eq777807 : x ≠ x ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5443 y x
       have i₂ := eq777767
       grind)
    | exact superpose eq777767 eq5443
    | (have j0 := eq5443 y x
       grind)
    | (have r₁ := eq5443 y x
       have r₂ := eq777767
       grind)
    | (have r₁ := eq5443 x x
       have r₂ := eq777767
       grind)
    | exact resolve eq5443 eq777767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5443
  have eq777824 : x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35731 x y
       have i₂ := eq777767
       grind)
    | exact superpose eq777767 eq35731
    | (have j0 := eq35731 x x
       grind)
    | exact resolve eq35731 eq777767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35731 eq777767
  have eq777847 : x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq777824
  have eq777863 : x ≠ x ∨ y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq777807
  have eq777864 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq777863
  have eq777879 : y = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq689 x
       grind)
    | (have r₁ := eq777847
       have r₂ := eq689 x
       grind)
    | exact resolve eq777847 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777847
  have eq777893 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq777864
       grind)
    | exact superpose eq777864 eq9
    | exact resolve eq9 eq777864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777864
  have eq778583 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ x = (M.op x y) ∨ x = (k x x) := by
    intro X0
    first
    | (have i₁ := eq777893 X0
       have i₂ := eq94 y X0
       grind)
    | exact superpose eq94 eq777893
    | exact resolve eq777893 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777893
  have eq778629 : y = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq94 y x
       have i₂ := eq777879
       grind)
    | exact superpose eq777879 eq94
    | exact resolve eq94 eq777879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777879
  have eq787577 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq778583 y
       have i₂ := eq778629
       grind)
    | exact superpose eq778629 eq778583
    | exact resolve eq778583 eq778629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778629
  have eq788557 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x x) := by grind
  clear eq787577
  have eq788565 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq689 x
       grind)
    | (have r₁ := eq788557
       have r₂ := eq689 x
       grind)
    | exact resolve eq788557 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788557
  have eq788984 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq778583 x
       have i₂ := eq788565
       grind)
    | exact superpose eq788565 eq778583
    | exact resolve eq778583 eq788565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778583 eq788565
  have eq789509 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (k x x) := by grind
  clear eq788984
  have eq789517 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have j1 := eq689 x
       grind)
    | (have r₁ := eq789509
       have r₂ := eq689 x
       grind)
    | exact resolve eq789509 eq689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689 eq789509
  have eq790495 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq94 x y
       have i₂ := eq789517
       grind)
    | exact superpose eq789517 eq94
    | exact resolve eq94 eq789517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789517
  have eq791021 : x = (M.op x x) := by grind
  clear eq790495
  have eq791227 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq79 x X0
       have i₂ := eq791021
       grind)
    | exact superpose eq791021 eq79
    | exact resolve eq79 eq791021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq791369 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq791021
       grind)
    | exact superpose eq791021 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq791021
       grind)
    | exact resolve eq12 eq791021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791422 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq441 x x x
       have i₂ := eq791021
       grind)
    | exact superpose eq791021 eq441
    | exact resolve eq441 eq791021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791795 : x = (k x x) := by grind
  clear eq791369
  have eq791936 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq791422 X0
       have i₂ := eq94 x X0
       grind)
    | exact superpose eq94 eq791422
    | exact resolve eq791422 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq791422
  have eq792231 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq679 x x
       have i₂ := eq791795
       grind)
    | exact superpose eq791795 eq679
    | (have j0 := eq679 x x
       grind)
    | exact resolve eq679 eq791795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq679 eq791795
  have eq792320 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq792231
  have eq792321 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq792320
  have eq796278 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq791227 X0
       have i₂ := eq791936 X0
       grind)
    | exact superpose eq791936 eq791227
    | exact resolve eq791227 eq791936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791227
  have eq796284 : ∀ X0 : G, x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq791936 X0
       have i₂ := eq796278 X0
       grind)
    | exact superpose eq796278 eq791936
    | exact resolve eq791936 eq796278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791936
  have eq796486 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq441 x X1 X0
       have i₂ := eq796278 X0
       grind)
    | exact superpose eq796278 eq441
    | exact resolve eq441 eq796278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq798100 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq796486 X0 X0
       have i₂ := eq796278 X0
       grind)
    | exact superpose eq796278 eq796486
    | exact resolve eq796486 eq796278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796486
  have eq836065 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op (M.op (M.op x (M.op (M.op x (M.op (M.op x (M.op (M.op x (M.op (M.op x (M.op x X1)) X2)) X3)) X4)) X5)) X0) x) X6)) X7) X0) X7) = X7 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq3177 x X0 x X1 X2 X3 X4 X5 X6 X7
       have i₂ := eq791021
       grind)
    | exact superpose eq791021 eq3177
    | exact resolve eq3177 eq791021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177 eq791021
  have eq837441 : ∀ X0 X6 X7 : G, (M.op (M.op (M.op (M.op X0 (M.op x X6)) X7) X0) X7) = X7 := by
    intro X0 X6 X7
    first
    | (have i₁ := eq836065 X0 x x x x x X6 X7
       have i₂ := eq796284 (M.op (M.op x (M.op (M.op x (M.op (M.op x (M.op (M.op x (M.op (M.op x (M.op x x)) x)) x)) x)) x)) X0)
       grind)
    | exact superpose eq796284 eq836065
    | exact resolve eq836065 eq796284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796284 eq836065
  have eq837481 : ∀ X0 X6 X7 : G, (M.op (M.op (M.op (M.op X0 X6) X7) X0) X7) = X7 := by
    intro X0 X6 X7
    first
    | (have i₁ := eq837441 X0 X6 X7
       have i₂ := eq796278 X6
       grind)
    | exact superpose eq796278 eq837441
    | exact resolve eq837441 eq796278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837441
  have eq866363 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq837481 (σ x) (σ x) X0
       have i₂ := eq792321
       grind)
    | exact superpose eq792321 eq837481
    | exact resolve eq837481 eq792321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792321 eq837481
  have eq868301 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq866363 X0
       have i₂ := eq798100 X0 (σ x)
       grind)
    | exact superpose eq798100 eq866363
    | exact resolve eq866363 eq798100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798100 eq866363
  have eq872827 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq868301 (σ y)
       grind)
    | exact superpose eq868301 eq16
    | exact resolve eq16 eq868301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868301
  have eq874711 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq872827
       have i₂ := eq796278 y
       grind)
    | exact superpose eq796278 eq872827
    | exact resolve eq872827 eq796278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796278 eq872827
  have eq874712 : False := by grind
  exact eq874712

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyy_pxx_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq183 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq188 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq180 eq183
    | exact resolve eq183 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq183
  have eq550 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq16
    | exact resolve eq16 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq555 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq185 eq188
    | exact resolve eq188 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq188
  have eq558 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq555 eq16
    | exact resolve eq16 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq564 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq550 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq550
    | exact resolve eq550 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq574 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq558 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq558
    | exact resolve eq558 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq596 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq598 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq670 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op y y) ∨ (k x y) = (M.op x x) := by
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
  have eq672 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq674 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq674 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq674 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq680 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq676 X0
       grind)
    | exact superpose eq676 eq13
    | exact resolve eq13 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X1
       have i₂ := eq676 (M.op X0 X1)
       grind)
    | exact superpose eq676 eq16
    | exact resolve eq16 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq976 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq681 (k (M.op X0 x) (M.op X0 x)) x
       have i₂ := eq681 X0 x
       grind)
    | exact superpose eq681 eq681
    | exact resolve eq681 eq681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq996 : ∀ X0 : G, (σ X0) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq976 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq976
    | exact resolve eq976 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1000 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (k X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (k X0 X0) X1
       have i₂ := eq976 X0
       grind)
    | exact superpose eq976 eq16
    | exact resolve eq16 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1001 : ∀ X0 X1 : G, (M.op (M.op (M.op (k X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (k X0 X0) X0
       have i₂ := eq976 X0
       grind)
    | exact superpose eq976 eq16
    | exact resolve eq16 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq1074 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ (k X0 X0)) X1) (σ X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (σ (k X0 X0)) (σ X0)
       have i₂ := eq996 X0
       grind)
    | exact superpose eq996 eq16
    | exact resolve eq16 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq2928 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq596
       grind)
    | exact superpose eq596 eq40
    | exact resolve eq40 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq2929 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2928
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2928
    | exact resolve eq2928 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928
  have eq2931 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2929
    | exact resolve eq2929 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2929
  have eq2933 : (M.op x y) = (k x x) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2931
       have i₂ := eq676 x
       grind)
    | exact superpose eq676 eq2931
    | exact resolve eq2931 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2931
  have eq2935 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq2933
       have i₂ := eq676 y
       grind)
    | exact superpose eq676 eq2933
    | exact resolve eq2933 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2933
  have eq3124 : (M.op x y) ≠ (k x x) ∨ y = (M.op y y) ∨ (k x x) = (k x y) := by
    first
    | (have i₁ := eq670
       have i₂ := eq676 x
       grind)
    | exact superpose eq676 eq670
    | exact resolve eq670 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq3125 : (M.op x y) ≠ (k x x) ∨ y = (k y y) ∨ (k x x) = (k x y) := by
    first
    | (have i₁ := eq3124
       have i₂ := eq676 y
       grind)
    | exact superpose eq676 eq3124
    | exact resolve eq3124 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124
  have eq3990 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq672
       have i₂ := eq676 sF2
       grind)
    | exact superpose eq676 eq672
    | exact resolve eq672 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq3991 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq3990
       have i₂ := eq676 sF3
       grind)
    | exact superpose eq676 eq3990
    | exact resolve eq3990 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3990
  have eq24135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq2935 eq598
    | exact resolve eq598 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24146 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | (have r₁ := eq24135
       have r₂ := eq27
       grind)
    | exact resolve eq24135 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24135
  have eq24154 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq24146
       have i₂ := eq676 sF2
       grind)
    | exact superpose eq676 eq24146
    | exact resolve eq24146 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24146
  have eq24158 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq24154
       have i₂ := eq676 sF3
       grind)
    | exact superpose eq676 eq24154
    | exact resolve eq24154 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24154
  have eq43162 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq24158 eq3991
    | (have r₁ := eq3991
       have r₂ := eq24158
       grind)
    | exact resolve eq3991 eq24158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991 eq24158
  have eq43163 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by grind
  clear eq43162
  have eq43164 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by grind
  clear eq43163
  have eq43165 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq2935 eq43164
    | exact resolve eq43164 eq2935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2935 eq43164
  have eq43166 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | (have r₁ := eq43165
       have r₂ := eq27
       grind)
    | exact resolve eq43165 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43165
  have eq43178 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq43166 eq152
    | exact resolve eq152 eq43166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43166
  have eq43216 : y = (k y y) ∨ (M.op x y) = (k x x) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq43178
    | exact resolve eq43178 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43178
  have eq43217 : (M.op x y) = (k x x) ∨ y = (k y y) := by grind
  clear eq43216
  have eq43248 : (M.op x y) ≠ (M.op x y) ∨ y = (k y y) ∨ (M.op x y) = (k x y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq3125
       have i₂ := eq43217
       grind)
    | exact superpose eq43217 eq3125
    | (have r₁ := eq3125
       have r₂ := eq43217
       grind)
    | exact resolve eq3125 eq43217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3125
  have eq43250 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq43217
       grind)
    | exact superpose eq43217 eq39
    | exact resolve eq39 eq43217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq43217
  have eq43272 : (M.op x y) ≠ (M.op x y) ∨ y = (k y y) ∨ (M.op x y) = (k x y) := by grind
  clear eq43248
  have eq43273 : (M.op x y) = (k x y) ∨ y = (k y y) := by grind
  clear eq43272
  have eq43281 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq43250
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43250
    | exact resolve eq43250 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43250
  have eq43298 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq43281
    | exact resolve eq43281 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43281
  have eq43371 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq43273
       grind)
    | exact superpose eq43273 eq40
    | exact resolve eq40 eq43273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43273
  have eq43374 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq43371
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43371
    | exact resolve eq43371 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq43371
  have eq43378 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq20 eq43374
    | exact resolve eq43374 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43374
  have eq43823 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq43378 eq598
    | exact resolve eq598 eq43378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq43378
  have eq43839 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq43823
       have r₂ := eq27
       grind)
    | exact resolve eq43823 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43823
  have eq43846 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq43839
       have i₂ := eq676 sF2
       grind)
    | exact superpose eq676 eq43839
    | exact resolve eq43839 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43839
  have eq43849 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq43846
       have i₂ := eq676 sF3
       grind)
    | exact superpose eq676 eq43846
    | exact resolve eq43846 eq676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676 eq43846
  have eq43852 : (σ y) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq43298 eq43849
    | exact resolve eq43849 eq43298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43298 eq43849
  have eq43855 : (σ y) = (k (σ y) (σ y)) ∨ y = (k y y) := by
    first
    | (have r₁ := eq43852
       have r₂ := eq27
       grind)
    | exact resolve eq43852 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43852
  have eq44090 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (k y y) := by
    first
    | exact superpose eq43855 eq152
    | exact resolve eq152 eq43855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq43855
  have eq44128 : y = (k y y) ∨ y = (k y y) := by
    first
    | exact superpose eq31 eq44090
    | exact resolve eq44090 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq44090
  have eq44129 : y = (k y y) := by grind
  clear eq44128
  have eq44154 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq44129
       grind)
    | exact superpose eq44129 eq40
    | exact resolve eq40 eq44129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq44157 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq680 y x
       have i₂ := eq44129
       grind)
    | exact superpose eq44129 eq680
    | (have r₁ := eq680 y x
       have r₂ := eq44129
       grind)
    | exact resolve eq680 eq44129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680
  have eq44164 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) := by
    intro X0
    first
    | (have i₁ := eq1000 y X0
       have i₂ := eq44129
       grind)
    | exact superpose eq44129 eq1000
    | exact resolve eq1000 eq44129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44165 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1001 y X0
       have i₂ := eq44129
       grind)
    | exact superpose eq44129 eq1001
    | exact resolve eq1001 eq44129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1001 eq44129
  have eq44176 : ∀ X0 : G, y = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq44157 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44157
  have eq44184 : ∀ X0 : G, y = (M.op (M.op y X0) y) := by
    intro X0
    first
    | (have i₁ := eq44164 X0
       have i₂ := eq564 X0
       grind)
    | exact superpose eq564 eq44164
    | exact resolve eq44164 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq44164
  have eq44190 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq44154
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44154
    | exact resolve eq44154 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44154
  have eq44382 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq44190 eq1000
    | exact resolve eq1000 eq44190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000 eq44190
  have eq44402 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq574 eq44382
    | exact resolve eq44382 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq44382
  have eq46433 : ∀ X0 : G, (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq44165 X0
       have i₂ := eq44184 X0
       grind)
    | exact superpose eq44184 eq44165
    | exact resolve eq44165 eq44184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46488 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op y X0) y) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op (M.op y X0) y) X0
       have i₂ := eq44165 X0
       grind)
    | exact superpose eq44165 eq16
    | exact resolve eq16 eq44165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44165
  have eq46526 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46488 X0 X1
       have i₂ := eq44184 X0
       grind)
    | exact superpose eq44184 eq46488
    | exact resolve eq46488 eq44184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46488
  have eq46560 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46526 X0 X1
       have i₂ := eq46433 X1
       grind)
    | exact superpose eq46433 eq46526
    | exact resolve eq46526 eq46433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46526
  have eq46602 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq44184 X0
       have i₂ := eq46433 X0
       grind)
    | exact superpose eq46433 eq44184
    | exact resolve eq44184 eq46433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44184 eq46433
  have eq47120 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq46602 x
       grind)
    | exact superpose eq46602 eq18
    | (have j1 := eq46602 x
       grind)
    | exact resolve eq18 eq46602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq46602
  have eq47269 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq47120
       grind)
    | exact superpose eq47120 eq24
    | exact resolve eq24 eq47120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq47348 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq44176 X0
       have i₂ := eq47120
       grind)
    | exact superpose eq47120 eq44176
    | exact resolve eq44176 eq47120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44176 eq47120
  have eq47391 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq47269 eq20
    | exact resolve eq20 eq47269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47269
  have eq48120 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq47348 eq1074
    | exact resolve eq1074 eq47348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074 eq47348
  have eq48212 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48120 X0
       have i₂ := eq46560 X0 (σ sF0)
       grind)
    | exact superpose eq46560 eq48120
    | exact resolve eq48120 eq46560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46560 eq48120
  have eq48250 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq48212
    | (have j0 := eq48212 X0
       grind)
    | exact resolve eq48212 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq48212
  have eq48267 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq47391 eq48250
    | exact resolve eq48250 eq47391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48250
  have eq48916 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq48267 eq44402
    | exact resolve eq44402 eq48267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44402 eq48267
  have eq49436 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48916 eq26
    | (have j1 := eq48916 (σ x)
       grind)
    | exact resolve eq26 eq48916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq48916
  have eq49536 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq49436 eq27
    | exact resolve eq27 eq49436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq49436
  have eq49781 : False := by grind
  exact eq49781
