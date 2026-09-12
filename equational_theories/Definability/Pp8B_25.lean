import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxy_pyx_x_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  clear eq43
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq64 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op X2 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X0) X1)
       have i₂ := eq14 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq113 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 X0) X2) X1) = (M.op X1 (M.op (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X2) X1
       have i₂ := eq14 (M.op X0 X0) X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X1) X2)
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X1) X2) X1
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq114 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq114 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq114 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq120 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq115 sF2
       grind)
    | exact superpose eq115 eq49
    | exact resolve eq49 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq121 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq120
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq120
    | exact resolve eq120 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq136 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq138 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq138
       have i₂ := eq115 sF1
       grind)
    | exact superpose eq115 eq138
    | exact resolve eq138 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq115 sF0
       grind)
    | exact superpose eq115 eq139
    | exact resolve eq139 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq139
  have eq433 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq939 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq433 X0 (M.op X0 X0)
       grind)
    | (have i₁ := eq64 X0 (M.op X0 X0) X2
       have i₂ := eq433 (M.op X0 X0) X1
       grind)
    | exact superpose eq433 eq64
    | (have r₁ := eq64 X1 (M.op X1 X1) X2
       have r₂ := eq433 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq64 X0 (M.op X0 X0) X2
       have r₂ := eq433 X0 (M.op X0 X0)
       grind)
    | exact resolve eq64 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq944 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq939 X0 x X2
       grind)
    | (have r₁ := eq939 X0 x X2
       have r₂ := eq433 X0 x
       grind)
    | (have r₁ := eq939 x X0 X2
       have r₂ := eq433 X0 x
       grind)
    | exact resolve eq939 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq939
  have eq1757 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X2) X1) = (M.op X1 (M.op (M.op X0 X0) X2)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq113 X0 X1 X2
       grind)
    | (have r₁ := eq113 X0 X1 X2
       have r₂ := eq433 X0 X1
       grind)
    | (have r₁ := eq113 X1 X0 X2
       have r₂ := eq433 X0 X1
       grind)
    | exact resolve eq113 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1775 : ∀ X0 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1757 (M.op x x) x (M.op X0 (M.op x x))
       have i₂ := eq14 X0 x (M.op x x)
       grind)
    | exact superpose eq14 eq1757
    | (have j0 := eq1757 X0 X2 X2
       grind)
    | exact resolve eq1757 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1848 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1775 y x
       grind)
    | exact superpose eq1775 eq71
    | (have j1 := eq1775 x x
       grind)
    | exact resolve eq71 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1870 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1848
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1848
    | exact resolve eq1848 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq1872 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1870
    | exact resolve eq1870 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1870
  have eq1875 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1872 eq1775
    | (have j0 := eq1775 x (σ x)
       grind)
    | exact resolve eq1775 eq1872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775 eq1872
  have eq1876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq1875
    | exact resolve eq1875 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875
  have eq1879 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1876
       have r₂ := eq27
       grind)
    | exact resolve eq1876 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1876
  have eq1886 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1879 eq121
    | exact resolve eq121 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq1879
  have eq1923 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq1886
    | exact resolve eq1886 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1886
  have eq1924 : x = (M.op x x) := by grind
  clear eq1923
  have eq1925 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq1924
       have i₂ := eq433 X0 x
       grind)
    | (have i₁ := eq1924
       have i₂ := eq433 x X0
       grind)
    | exact superpose eq433 eq1924
    | exact resolve eq1924 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq1959 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq944 x x
       have i₂ := eq1924
       grind)
    | exact superpose eq1924 eq944
    | exact resolve eq944 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944 eq1924
  have eq2022 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X1
       have i₂ := eq1925 X1
       grind)
    | exact superpose eq1925 eq14
    | exact resolve eq14 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2035 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq1925 (M.op X0 X0)
       grind)
    | exact superpose eq1925 eq14
    | exact resolve eq14 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2046 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq1925 sF0
       grind)
    | exact superpose eq1925 eq142
    | exact resolve eq142 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq2054 : x = (σ x) := by
    first
    | (have i₁ := eq2046
       have i₂ := eq1925 sF1
       grind)
    | exact superpose eq1925 eq2046
    | exact resolve eq2046 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2046
  have eq2062 : ∀ X1 : G, (M.op x (M.op X1 x)) = X1 := by
    intro X1
    first
    | (have i₁ := eq2035 x X1
       have i₂ := eq1925 x
       grind)
    | exact superpose eq1925 eq2035
    | exact resolve eq2035 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq2067 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 := by
    intro X1
    first
    | (have i₁ := eq2022 x X1
       have i₂ := eq1925 x
       grind)
    | exact superpose eq1925 eq2022
    | exact resolve eq2022 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925 eq2022
  have eq2093 : x = (σ x) := by
    first
    | (have i₁ := eq2054
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2054
    | exact resolve eq2054 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2054
  have eq2112 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq2093 eq26
    | exact resolve eq26 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2254 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq136
       have i₂ := eq1959 sF0
       grind)
    | exact superpose eq1959 eq136
    | exact resolve eq136 eq1959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq2261 : (σ (M.op (M.op x y) x)) = (k (σ (M.op x y)) x) := by
    first
    | exact superpose eq2093 eq2254
    | exact resolve eq2254 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093 eq2254
  have eq2268 : (σ (M.op (M.op x y) x)) = (M.op (σ (M.op x y)) x) := by
    first
    | (have i₁ := eq2261
       have i₂ := eq1959 sF1
       grind)
    | exact superpose eq1959 eq2261
    | exact resolve eq2261 eq1959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1959 eq2261
  have eq2381 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2067 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2067
    | (have j0 := eq2067 y
       grind)
    | exact resolve eq2067 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2067
  have eq2686 : (σ y) = (M.op (σ (M.op x y)) x) := by
    first
    | exact superpose eq2381 eq2268
    | exact resolve eq2268 eq2381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268 eq2381
  have eq2687 : (σ y) = (M.op (σ (M.op x y)) x) := by
    first
    | (have i₁ := eq2686
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2686
    | exact resolve eq2686 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2686
  have eq2688 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq2687 eq2062
    | exact resolve eq2062 eq2687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2062 eq2687
  have eq2693 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2112 eq2688
    | exact resolve eq2688 eq2112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2112 eq2688
  have eq2696 : False := by grind
  exact eq2696

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = m(Y,Y) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_x_pxy_x_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq11 (M.op X1 X1) X1
       have r₂ := eq13 X0 (M.op X1 X1)
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
  have eq177 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq539 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq176 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq539 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq539 X1 X0
       grind)
    | exact superpose eq539 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq539 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq539 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq539 X0 X2
       grind)
    | (have i₁ := eq16 X2 X1 X2
       have i₂ := eq539 X2 X0
       grind)
    | exact superpose eq539 eq16
    | exact resolve eq16 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq539 X2 (M.op X1 (M.op X0 X0))
       grind)
    | (have i₁ := eq176 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq539 (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact superpose eq539 eq176
    | exact resolve eq176 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq786 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X0 X0) = X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X2 X0
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq794 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 X0) X2) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X2) X1
       have i₂ := eq16 (M.op X0 X0) X0 X2
       grind)
    | exact superpose eq16 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X1) X2)
       have r₂ := eq16 (M.op X1 X1) X1 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X1) X2) X1
       have r₂ := eq16 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X2) X1) = (M.op (M.op (M.op X0 X0) X2) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq794 X0 X1 X2
       grind)
    | (have r₁ := eq794 X0 X1 X2
       have r₂ := eq539 X0 X1
       grind)
    | (have r₁ := eq794 X1 X0 X2
       have r₂ := eq539 X0 X1
       grind)
    | exact resolve eq794 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq804 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq786 X0 X1 X2
       have j1 := eq559 X0 (M.op X2 X2) X2
       grind)
    | (have r₁ := eq786 X0 X1 X2
       have r₂ := eq559 X0 X1 X2
       grind)
    | (have r₁ := eq786 X0 (M.op X0 X0) X2
       have r₂ := eq559 X0 (M.op X0 X0) X2
       grind)
    | (have r₁ := eq786 X0 X0 X0
       have r₂ := eq559 X0 (k X0 X0) X2
       grind)
    | exact resolve eq786 eq559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559 eq786
  have eq806 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X2 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq804 X0 X1 X2
       grind)
    | (have r₁ := eq804 X1 X1 X0
       have r₂ := eq539 X0 X1
       grind)
    | (have r₁ := eq804 X0 X1 X1
       have r₂ := eq539 X0 X1
       grind)
    | exact resolve eq804 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq1171 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X0) = (M.op (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 (M.op X1 X1) X1 (M.op (M.op X2 X2) X0)
       have i₂ := eq564 (M.op X1 X1) X2 X0
       grind)
    | exact superpose eq564 eq176
    | exact resolve eq176 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1987 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq795 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq2110 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq806 X0 y x
       grind)
    | exact superpose eq806 eq18
    | (have j1 := eq806 X0 y x
       grind)
    | exact resolve eq18 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2111 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq806 X0 sF3 sF2
       grind)
    | exact superpose eq806 eq26
    | (have j1 := eq806 X0 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq2404 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq41 x
       have i₂ := eq2110 X0
       grind)
    | (have i₁ := eq41 X0
       have i₂ := eq2110 X0
       grind)
    | exact superpose eq2110 eq41
    | (have j1 := eq2110 X0
       grind)
    | exact resolve eq41 eq2110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2110
  have eq2406 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq2404 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2404
    | (have j0 := eq2404 X0
       grind)
    | exact resolve eq2404 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2404
  have eq2408 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq2406
    | (have j0 := eq2406 X0
       grind)
    | exact resolve eq2406 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2406
  have eq2417 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2111 X0
       have i₂ := eq2408 (k sF2 sF3)
       grind)
    | exact superpose eq2408 eq2111
    | (have j0 := eq2111 X0
       have j1 := eq2408 X1
       grind)
    | exact resolve eq2111 eq2408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2111 eq2408
  have eq2424 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2417 X0 X1
       grind)
    | (have r₁ := eq2417 X0 X1
       have r₂ := eq27
       grind)
    | exact resolve eq2417 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417
  have eq2435 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq37 y
       have i₂ := eq2424 X0 y
       grind)
    | exact superpose eq2424 eq37
    | (have j1 := eq2424 (σ y) x
       grind)
    | exact resolve eq37 eq2424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq2424
  have eq2445 : ∀ X0 : G, (σ y) = (k (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2435 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2435
    | (have j0 := eq2435 (σ y)
       grind)
    | exact resolve eq2435 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2435
  have eq2587 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
    first
    | (have j0 := eq2445 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2445
  have eq2588 : (σ y) = (k (σ y) (σ y)) := by grind
  clear eq2587
  have eq2595 : (τ (σ y)) = (k (τ (σ y)) y) := by
    first
    | exact superpose eq2588 eq153
    | exact resolve eq153 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq2596 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2588 eq1987
    | (have j0 := eq1987 (σ y)
       grind)
    | (have r₁ := eq1987 (σ y)
       have r₂ := eq2588
       grind)
    | exact resolve eq1987 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2588
  have eq2597 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2596
  have eq2598 : y = (k y y) := by
    first
    | exact superpose eq32 eq2595
    | exact resolve eq2595 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2595
  have eq2651 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq2597 eq539
    | exact resolve eq539 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq2658 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq2597 eq566
    | exact resolve eq566 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq2697 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ y) X1) := by
    intro X0 X1
    first
    | exact superpose eq2597 eq1171
    | exact resolve eq1171 eq2597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171 eq2597
  have eq2730 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1987 y
       have i₂ := eq2598
       grind)
    | exact superpose eq2598 eq1987
    | (have j0 := eq1987 y
       grind)
    | (have r₁ := eq1987 y
       have r₂ := eq2598
       grind)
    | exact resolve eq1987 eq2598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1987 eq2598
  have eq2731 : y = (M.op y y) := by grind
  clear eq2730
  have eq2732 : y = (σ y) := by
    first
    | (have i₁ := eq2731
       have i₂ := eq2651 y
       grind)
    | exact superpose eq2651 eq2731
    | exact resolve eq2731 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2731
  have eq2735 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2732
       grind)
    | exact superpose eq2732 eq24
    | exact resolve eq24 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq2738 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) (σ y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq2732
       grind)
    | exact superpose eq2732 eq177
    | exact resolve eq177 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2747 : x = (M.op (M.op (σ y) (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq2738 x
       have i₂ := eq2697 x sF3
       grind)
    | exact superpose eq2697 eq2738
    | exact resolve eq2738 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738
  have eq2749 : x = (M.op (σ y) (M.op x y)) := by
    first
    | (have i₁ := eq2747
       have i₂ := eq2697 sF3 sF0
       grind)
    | exact superpose eq2697 eq2747
    | exact resolve eq2747 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747
  have eq3229 : ∀ X0 X1 X2 : G, (M.op (k (M.op (M.op X0 X0) (M.op X0 X0)) X1) (M.op X2 X2)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq564 X2 (M.op X0 X0) X1
       have i₂ := eq796 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq796 eq564
    | (have j1 := eq796 X0 X1 X2
       grind)
    | exact resolve eq564 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq3239 : ∀ X0 : G, x = (k (M.op (M.op X0 X0) y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq796 X0 sF0 y
       grind)
    | exact superpose eq796 eq177
    | (have j1 := eq796 X0 (M.op x y) x
       grind)
    | exact resolve eq177 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq796
  have eq3320 : x = (k (M.op (σ y) y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3239 x
       have i₂ := eq2697 x y
       grind)
    | exact superpose eq2697 eq3239
    | exact resolve eq3239 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239
  have eq3327 : ∀ X0 X1 : G, (M.op (k (M.op (M.op X0 X0) (M.op X0 X0)) X1) (σ y)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3229 X0 X1 x
       have i₂ := eq2658 (k (M.op (M.op X0 X0) (M.op X0 X0)) X1) x
       grind)
    | exact superpose eq2658 eq3229
    | (have j0 := eq3229 X0 X1 x
       grind)
    | exact resolve eq3229 eq2658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229
  have eq3346 : x = (k (M.op (σ y) (σ y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3320
       have i₂ := eq2732
       grind)
    | exact superpose eq2732 eq3320
    | exact resolve eq3320 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3320
  have eq3353 : ∀ X0 X1 : G, (M.op (k (M.op (σ y) (M.op X0 X0)) X1) (σ y)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3327 X0 X1
       have i₂ := eq2697 X0 (M.op X0 X0)
       grind)
    | exact superpose eq2697 eq3327
    | (have j0 := eq3327 X0 X1
       grind)
    | exact resolve eq3327 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697 eq3327
  have eq3372 : x = (k (σ y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq3346
       have i₂ := eq2651 sF3
       grind)
    | exact superpose eq2651 eq3346
    | exact resolve eq3346 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346
  have eq3377 : ∀ X1 : G, (M.op (k (M.op (σ y) (σ y)) X1) (σ y)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq3353 X1 X1
       have i₂ := eq2658 sF3 X1
       grind)
    | exact superpose eq2658 eq3353
    | (have j0 := eq3353 x X1
       grind)
    | exact resolve eq3353 eq2658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2658 eq3353
  have eq3394 : x = (k (σ y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq3372
       have i₂ := eq2651 sF0
       grind)
    | exact superpose eq2651 eq3372
    | exact resolve eq3372 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3372
  have eq3399 : ∀ X1 : G, (M.op (k (σ y) X1) (σ y)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq3377 X1
       have i₂ := eq2651 sF3
       grind)
    | exact superpose eq2651 eq3377
    | (have j0 := eq3377 X1
       grind)
    | exact resolve eq3377 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377
  have eq3411 : ∀ X1 : G, (M.op (k (σ y) X1) (σ y)) = X1 ∨ (σ y) = X1 := by
    intro X1
    first
    | (have i₁ := eq3399 X1
       have i₂ := eq2651 X1
       grind)
    | exact superpose eq2651 eq3399
    | (have j0 := eq3399 X1
       grind)
    | exact resolve eq3399 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399
  have eq4142 : (σ x) = (k (σ (σ y)) (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq3394 eq42
    | exact resolve eq42 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq3394
  have eq4143 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq2735 eq4142
    | exact resolve eq4142 eq2735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4142
  have eq4145 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq4143
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4143
    | exact resolve eq4143 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4143
  have eq7393 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq4145 eq3411
    | (have j0 := eq3411 (σ (M.op x y))
       grind)
    | exact resolve eq3411 eq4145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3411 eq4145
  have eq7453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26 eq7393
    | exact resolve eq7393 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7393
  have eq7479 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq7453
       have r₂ := eq27
       grind)
    | exact resolve eq7453 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7453
  have eq7519 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq7479 eq29
    | exact resolve eq29 eq7479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq7479
  have eq7551 : y = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq32 eq7519
    | exact resolve eq7519 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq7519
  have eq7561 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq7551
       have i₂ := eq2732
       grind)
    | exact superpose eq2732 eq7551
    | exact resolve eq7551 eq2732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732 eq7551
  have eq7562 : (M.op x y) = (σ y) := by grind
  clear eq7561
  have eq7613 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq7562 eq2735
    | exact resolve eq2735 eq7562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2735
  have eq7615 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7562 eq2749
    | exact resolve eq2749 eq7562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq7623 : x = (σ y) := by
    first
    | (have i₁ := eq7615
       have i₂ := eq2651 sF0
       grind)
    | exact superpose eq2651 eq7615
    | exact resolve eq7615 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7615
  have eq7647 : x = (M.op x y) := by
    first
    | exact superpose eq7562 eq7623
    | exact resolve eq7623 eq7562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7623
  have eq7713 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq7647
       grind)
    | exact superpose eq7647 eq22
    | exact resolve eq22 eq7647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7647
  have eq7736 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq7613 eq7713
    | exact resolve eq7713 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7713
  have eq7741 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq7736 eq26
    | exact resolve eq26 eq7736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq7736
  have eq7774 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7562 eq7741
    | exact resolve eq7741 eq7562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7741
  have eq7783 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7774
       have i₂ := eq2651 sF0
       grind)
    | exact superpose eq2651 eq7774
    | exact resolve eq7774 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651 eq7774
  have eq7790 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7562 eq7783
    | exact resolve eq7783 eq7562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7562 eq7783
  have eq7797 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq7790 eq27
    | exact resolve eq27 eq7790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7790
  have eq7816 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq7613 eq20
    | exact resolve eq20 eq7613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq7613
  have eq7836 : False := by grind
  exact eq7836

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = m(Y,Y) then m(Y,X) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_x_pyx_y_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  clear eq35
  have eq60 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq61 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq110 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op X1 X1) X2)
       have i₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X2 X0
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X1) X2)
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X1) X2) X1
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k (M.op (M.op X0 X0) X2) X1) = (M.op X1 (M.op (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X2) X1
       have i₂ := eq14 (M.op X0 X0) X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X1) X2)
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X1) X2) X1
       have r₂ := eq14 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq307 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq326 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq60 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq60 eq60
    | exact resolve eq60 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq346 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq326 X0 X1
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq326 X1 X0
       grind)
    | exact superpose eq326 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq326 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq326 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq655 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq346 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq665 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 (M.op X1 X1)
       have i₂ := eq655 (σ X0) X1
       grind)
    | exact superpose eq655 eq307
    | exact resolve eq307 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307 eq655
  have eq668 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq665 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq665
    | exact resolve eq665 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq1558 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X2) X1) = (M.op X1 (M.op (M.op X0 X0) X2)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq113 X0 X1 X2
       grind)
    | (have r₁ := eq113 X0 X1 X2
       have r₂ := eq326 X0 X1
       grind)
    | (have r₁ := eq113 X1 X0 X2
       have r₂ := eq326 X0 X1
       grind)
    | exact resolve eq113 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1672 : ∀ X0 X2 : G, (k X0 X2) = (M.op X2 X0) ∨ (M.op X2 X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq1558 (M.op x x) x (M.op X0 (M.op x x))
       have i₂ := eq14 X0 x (M.op x x)
       grind)
    | exact superpose eq14 eq1558
    | (have j0 := eq1558 X0 X2 X2
       grind)
    | exact resolve eq1558 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558
  have eq1763 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq1672 y x
       grind)
    | exact superpose eq1672 eq71
    | (have j1 := eq1672 x x
       grind)
    | exact resolve eq71 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1786 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1763
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1763
    | exact resolve eq1763 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763
  have eq1788 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1786
    | exact resolve eq1786 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1788 eq1672
    | (have j0 := eq1672 x (σ x)
       grind)
    | exact resolve eq1672 eq1788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1788
  have eq1793 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq1792
    | exact resolve eq1792 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq1796 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1793
       have r₂ := eq27
       grind)
    | exact resolve eq1793 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793
  have eq1825 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1796 eq668
    | exact resolve eq668 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq1796
  have eq1842 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq28 eq1825
    | exact resolve eq1825 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825
  have eq1844 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq1842 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq1842 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1842 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq1851 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1844 x
       grind)
    | exact superpose eq1844 eq43
    | exact resolve eq43 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1854 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq114 x
       have i₂ := eq1844 x
       grind)
    | exact superpose eq1844 eq114
    | (have j0 := eq114 x
       grind)
    | exact resolve eq114 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1844
  have eq1859 : x = (M.op x x) := by grind
  clear eq1854
  have eq1865 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1851
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1851
    | exact resolve eq1851 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851
  have eq1868 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq1859
       have i₂ := eq326 X0 x
       grind)
    | (have i₁ := eq1859
       have i₂ := eq326 x X0
       grind)
    | exact superpose eq326 eq1859
    | exact resolve eq1859 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1930 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1865 eq1672
    | (have j0 := eq1672 x (σ x)
       grind)
    | exact resolve eq1672 eq1865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672 eq1865
  have eq1931 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1930
  have eq2014 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X1
       have i₂ := eq1868 X1
       grind)
    | exact superpose eq1868 eq14
    | exact resolve eq14 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2042 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 := by
    intro X1
    first
    | (have i₁ := eq2014 x X1
       have i₂ := eq1868 x
       grind)
    | exact superpose eq1868 eq2014
    | exact resolve eq2014 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014
  have eq2263 : x = (σ x) := by
    first
    | (have i₁ := eq1931
       have i₂ := eq1868 sF2
       grind)
    | exact superpose eq1868 eq1931
    | exact resolve eq1931 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq2264 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq2263 eq26
    | exact resolve eq26 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2265 : x = (τ x) := by
    first
    | exact superpose eq2263 eq28
    | exact resolve eq28 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2335 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq110 X0 X1 X2
       grind)
    | (have r₁ := eq110 X1 X1 X0
       have r₂ := eq326 X0 X1
       grind)
    | (have r₁ := eq110 X0 X1 X1
       have r₂ := eq326 X0 X1
       grind)
    | exact resolve eq110 eq326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq326
  have eq2336 : ∀ X0 X1 X2 : G, x = (M.op x X1) ∨ (k X2 (M.op (M.op X0 X0) X1)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2335 X0 X1 X2
       have i₂ := eq1868 X0
       grind)
    | exact superpose eq1868 eq2335
    | (have j0 := eq2335 X0 X1 X2
       grind)
    | exact resolve eq2335 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2335
  have eq2337 : ∀ X1 X2 : G, (k X2 (M.op x X1)) = (M.op (M.op x X1) X2) ∨ x = (M.op x X1) := by
    intro X1 X2
    first
    | (have i₁ := eq2336 x X1 X2
       have i₂ := eq1868 x
       grind)
    | exact superpose eq1868 eq2336
    | (have j0 := eq2336 x X1 X2
       grind)
    | exact resolve eq2336 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2336
  have eq2341 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2337 y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2337
    | (have j0 := eq2337 y X0
       grind)
    | exact resolve eq2337 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2347 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ x = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2337 (M.op x (M.op x (M.op X1 X1))) x
       have i₂ := eq60 x X1 x
       grind)
    | exact superpose eq60 eq2337
    | exact resolve eq2337 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq2337
  have eq2360 : (k (σ x) (σ (M.op x y))) = (σ (M.op (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2341 eq45
    | exact resolve eq45 eq2341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq2341
  have eq2367 : (σ (M.op (M.op x y) x)) = (k x (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2263 eq2360
    | exact resolve eq2360 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2661 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2042 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2042
    | (have j0 := eq2042 y
       grind)
    | exact resolve eq2042 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4770 : (σ y) = (k x (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2661 eq2367
    | exact resolve eq2367 eq2661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2367 eq2661
  have eq4771 : (σ y) = (k x (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4770
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4770
    | exact resolve eq4770 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4770
  have eq4772 : (σ y) = (M.op (σ (M.op x y)) x) ∨ x = (M.op x y) ∨ x = (σ (M.op x y)) := by
    first
    | (have i₁ := eq4771
       have i₂ := eq2347 sF1 x
       grind)
    | exact superpose eq2347 eq4771
    | (have j1 := eq2347 (M.op x y) x
       grind)
    | exact resolve eq4771 eq2347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2347 eq4771
  have eq5625 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (M.op X0 X0) x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4772 eq14
    | exact resolve eq14 eq4772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4772
  have eq5628 : (σ (M.op x y)) = (M.op (M.op x x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ (M.op x y)) := by
    first
    | (have i₁ := eq5625 x
       have i₂ := eq1868 x
       grind)
    | exact superpose eq1868 eq5625
    | exact resolve eq5625 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5625
  have eq5634 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op x y) ∨ x = (σ (M.op x y)) := by
    first
    | (have i₁ := eq5628
       have i₂ := eq1859
       grind)
    | exact superpose eq1859 eq5628
    | exact resolve eq5628 eq1859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5628
  have eq5638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (σ (M.op x y)) := by
    first
    | exact superpose eq2264 eq5634
    | exact resolve eq5634 eq2264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264 eq5634
  have eq5641 : x = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq5638
       have r₂ := eq27
       grind)
    | exact resolve eq5638 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5638
  have eq5643 : (M.op x y) = (τ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5641 eq30
    | exact resolve eq30 eq5641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5641
  have eq5669 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5643
       have i₂ := eq2265
       grind)
    | exact superpose eq2265 eq5643
    | exact resolve eq5643 eq2265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265 eq5643
  have eq5670 : x = (M.op x y) := by grind
  clear eq5669
  have eq5681 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq5670 eq20
    | exact resolve eq20 eq5670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq5683 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) x) := by
    intro X0
    first
    | exact superpose eq5670 eq61
    | exact resolve eq61 eq5670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq5670
  have eq5714 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq5683 x
       have i₂ := eq1868 x
       grind)
    | exact superpose eq1868 eq5683
    | exact resolve eq5683 eq1868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1868 eq5683
  have eq5716 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5681
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5681
    | exact resolve eq5681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5681
  have eq5725 : x = y := by
    first
    | (have i₁ := eq5714
       have i₂ := eq2042 y
       grind)
    | (have i₁ := eq5714
       have i₂ := eq2042 (M.op (M.op x y) x)
       grind)
    | exact superpose eq2042 eq5714
    | exact resolve eq5714 eq2042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042 eq5714
  have eq5727 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq2263 eq5716
    | exact resolve eq5716 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5716
  have eq5735 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5725
       grind)
    | exact superpose eq5725 eq24
    | exact resolve eq24 eq5725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq5725
  have eq5770 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq5735
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5735
    | exact resolve eq5735 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5735
  have eq5785 : x = (σ y) := by
    first
    | exact superpose eq2263 eq5770
    | exact resolve eq5770 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5770
  have eq6019 : (M.op (σ x) (σ y)) = (M.op (σ x) x) := by
    first
    | exact superpose eq5785 eq26
    | exact resolve eq26 eq5785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5785
  have eq6058 : (M.op (σ x) (σ y)) = (M.op x x) := by
    first
    | exact superpose eq2263 eq6019
    | exact resolve eq6019 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263 eq6019
  have eq6071 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6058
       have i₂ := eq1859
       grind)
    | exact superpose eq1859 eq6058
    | exact resolve eq6058 eq1859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859 eq6058
  have eq6088 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq6071 eq27
    | exact resolve eq27 eq6071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6071
  have eq6103 : False := by grind
  exact eq6103

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxy_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
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
  have eq74 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
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
  have eq98 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq74 x y
       grind)
    | exact superpose eq74 eq44
    | (have j1 := eq74 x x
       grind)
    | exact resolve eq44 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq106
    | exact resolve eq106 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq106
  have eq122 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  clear eq37
  have eq391 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq51 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq107 eq74
    | (have j0 := eq74 (σ x) x
       grind)
    | exact resolve eq74 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq688
    | exact resolve eq688 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq692 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq689
       have r₂ := eq27
       grind)
    | exact resolve eq689 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq697 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq692 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq692
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq692
       grind)
    | exact resolve eq13 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq707 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq697 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq888 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq707 eq49
    | exact resolve eq49 eq707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq707
  have eq1055 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq692 eq888
    | exact resolve eq888 eq692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692 eq888
  have eq1071 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by grind
  clear eq1055
  have eq1074 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq1071
    | exact resolve eq1071 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1071
  have eq1079 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq74 x x
       have i₂ := eq1074
       grind)
    | exact superpose eq1074 eq74
    | (have j0 := eq74 x x
       grind)
    | exact resolve eq74 eq1074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq1080 : x = (M.op x x) := by grind
  clear eq1079
  have eq1130 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq1080
       have i₂ := eq391 X0 x
       grind)
    | (have i₁ := eq1080
       have i₂ := eq391 x X0
       grind)
    | exact superpose eq391 eq1080
    | exact resolve eq1080 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq1133 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1080
       grind)
    | exact superpose eq1080 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1080
       grind)
    | exact resolve eq13 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1152 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1133 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1133
  have eq1190 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 X1
       have i₂ := eq1130 X1
       grind)
    | exact superpose eq1130 eq14
    | exact resolve eq14 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 X1 : G, (M.op x (M.op X1 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X0 X0)
       have i₂ := eq1130 (M.op X0 X0)
       grind)
    | exact superpose eq1130 eq14
    | exact resolve eq14 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1205 : ∀ X1 : G, (M.op x (M.op X1 x)) = X1 := by
    intro X1
    first
    | (have i₁ := eq1201 x X1
       have i₂ := eq1130 x
       grind)
    | exact superpose eq1130 eq1201
    | exact resolve eq1201 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1211 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 := by
    intro X1
    first
    | (have i₁ := eq1190 x X1
       have i₂ := eq1130 x
       grind)
    | exact superpose eq1130 eq1190
    | exact resolve eq1190 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1190
  have eq1255 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1152 x
       grind)
    | exact superpose eq1152 eq43
    | exact resolve eq43 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1257 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq122
       have i₂ := eq1152 sF0
       grind)
    | exact superpose eq1152 eq122
    | exact resolve eq122 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq1263 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1255
       have i₂ := eq1080
       grind)
    | exact superpose eq1080 eq1255
    | exact resolve eq1255 eq1080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1080 eq1255
  have eq1264 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1263
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1263
    | exact resolve eq1263 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1263
  have eq1271 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1264 eq74
    | (have j0 := eq74 (σ x) x
       grind)
    | exact resolve eq74 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq1264
  have eq1272 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1271
  have eq1274 : x = (σ x) := by
    first
    | (have i₁ := eq1272
       have i₂ := eq1130 sF2
       grind)
    | exact superpose eq1130 eq1272
    | exact resolve eq1272 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130 eq1272
  have eq1280 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1274 eq26
    | exact resolve eq26 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1422 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq1211 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1211
    | (have j0 := eq1211 y
       grind)
    | exact resolve eq1211 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1211
  have eq1509 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq1422 eq1257
    | exact resolve eq1257 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257 eq1422
  have eq1510 : (σ y) = (k (σ (M.op x y)) x) := by
    first
    | exact superpose eq1274 eq1509
    | exact resolve eq1509 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1274 eq1509
  have eq1511 : (σ y) = (M.op (σ (M.op x y)) x) := by
    first
    | (have i₁ := eq1510
       have i₂ := eq1152 sF1
       grind)
    | exact superpose eq1152 eq1510
    | exact resolve eq1510 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152 eq1510
  have eq1512 : (σ y) = (M.op (σ (M.op x y)) x) := by
    first
    | (have i₁ := eq1511
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1511
    | exact resolve eq1511 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1511
  have eq1513 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq1512 eq1205
    | exact resolve eq1205 eq1512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1205 eq1512
  have eq1518 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1280 eq1513
    | exact resolve eq1513 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280 eq1513
  have eq1521 : False := by grind
  exact eq1521

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_x_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq98 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 y
       grind)
    | exact resolve eq44 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq176 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
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
  have eq364 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
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
  clear eq307
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
  clear eq175
  have eq558 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
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
  have eq571 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq558 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq575 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq364 X0 (M.op X1 X1)
       have i₂ := eq571 (σ X0) X1
       grind)
    | exact superpose eq571 eq364
    | exact resolve eq364 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364 eq571
  have eq590 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq575
    | exact resolve eq575 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq726 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1 X1
       have i₂ := eq538 X0 X1
       grind)
    | (have i₁ := eq11 X0 X0
       have i₂ := eq538 X0 X1
       grind)
    | exact superpose eq538 eq11
    | (have j0 := eq11 X0 (k X1 X1)
       grind)
    | exact resolve eq11 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq538 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq538
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq756 : ∀ X0 X1 X2 : G, (M.op (k (M.op X0 X0) X1) (M.op X2 X1)) = X2 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq11 (M.op X0 X0) X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op X0 X0) X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq757 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X1) (M.op X2 X1)) = X2 ∨ (M.op X2 X1) = (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) ∨ (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1
       have i₂ := eq11 (M.op (M.op X0 X0) X1) (M.op X2 X1)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 (M.op (M.op X0 X0) X1) (M.op X2 X1)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq763 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq765 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq766 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq781 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq738 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738
  have eq787 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq732 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq788 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq726 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq726
  have eq792 : ∀ X0 X1 X2 : G, (k (M.op (M.op X0 X0) X1) (M.op X2 X1)) = X2 ∨ (M.op X0 X0) = (M.op X2 X1) ∨ (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq757 X0 X1 X2
       have i₂ := eq16 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq16 eq757
    | (have j0 := eq757 X0 X1 X2
       grind)
    | exact resolve eq757 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq793 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq787 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq787 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq787 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq787 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq905 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq766 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq766
    | (have j0 := eq766 (σ X0)
       grind)
    | exact resolve eq766 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq917 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq793 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq793
    | (have j0 := eq793 (σ X0) X1
       grind)
    | exact resolve eq793 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq2198 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq762
       grind)
    | exact superpose eq762 eq40
    | exact resolve eq40 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq2199 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2198
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2198
    | exact resolve eq2198 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2201 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2199
    | exact resolve eq2199 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq2307 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq766 X1
       have i₂ := eq781 X1 X0
       grind)
    | exact superpose eq781 eq766
    | (have j0 := eq766 X1
       have j1 := eq781 X1 X1
       grind)
    | (have r₁ := eq766 (M.op X1 X1)
       have r₂ := eq781 (M.op X1 X1) X1
       grind)
    | exact resolve eq766 eq781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766 eq781
  have eq2325 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2307 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq2471 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq590 (τ (M.op X1 X1)) X1
       have i₂ := eq788 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq788 eq590
    | (have j1 := eq788 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq590 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2479 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq788 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq2483 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2471 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2471
  have eq2643 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (σ X2)) = (σ (k (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 (M.op X1 X1) X2
       have i₂ := eq2483 X0 X1
       grind)
    | exact superpose eq2483 eq34
    | exact resolve eq34 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq2483
  have eq3638 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op X1 X1) = (τ X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2479 X1 (τ X0)
       have i₂ := eq391 X0 X0
       grind)
    | exact superpose eq391 eq2479
    | (have j0 := eq2479 X1 (τ X0)
       grind)
    | exact resolve eq2479 eq391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq5268 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq763 eq98
    | exact resolve eq98 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq763
  have eq5273 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq2325 x (σ y)
       grind)
    | (have r₁ := eq5268
       have r₂ := eq2325 (σ x) (σ y)
       grind)
    | (have r₁ := eq5268
       have r₂ := eq2325 (σ y) (σ y)
       grind)
    | exact resolve eq5268 eq2325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5268
  have eq5480 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq5273
       grind)
    | exact superpose eq5273 eq40
    | exact resolve eq40 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq5273
  have eq5481 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5480
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq5480
    | exact resolve eq5480 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5480
  have eq5485 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5481
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5481
    | exact resolve eq5481 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5481
  have eq226620 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2201 eq5485
    | exact resolve eq5485 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201 eq5485
  have eq226631 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq2325 x (σ y)
       grind)
    | (have r₁ := eq226620
       have r₂ := eq2325 (σ y) (σ y)
       grind)
    | (have r₁ := eq226620
       have r₂ := eq2325 x y
       grind)
    | (have r₁ := eq226620
       have r₂ := eq2325 y y
       grind)
    | exact resolve eq226620 eq2325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226620
  have eq226641 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq226631
       have r₂ := eq27
       grind)
    | exact resolve eq226631 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226631
  have eq227368 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq226641 eq590
    | exact resolve eq590 eq226641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590 eq226641
  have eq228206 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq31 eq227368
    | exact resolve eq227368 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227368
  have eq228513 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq228206 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq228206 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq228206 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228206
  have eq228759 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq905 y
       have i₂ := eq228513 y
       grind)
    | exact superpose eq228513 eq905
    | (have j0 := eq905 y
       grind)
    | exact resolve eq905 eq228513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq228760 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq917 y X0
       have i₂ := eq228513 y
       grind)
    | exact superpose eq228513 eq917
    | (have j0 := eq917 y X0
       grind)
    | exact resolve eq917 eq228513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq228765 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq2479 X0 y
       have i₂ := eq228513 y
       grind)
    | exact superpose eq228513 eq2479
    | (have j0 := eq2479 X0 y
       grind)
    | (have r₁ := eq2479 X0 y
       have r₂ := eq228513 y
       grind)
    | exact resolve eq2479 eq228513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq228771 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have i₁ := eq3638 y X0
       have i₂ := eq228513 y
       grind)
    | exact superpose eq228513 eq3638
    | (have j0 := eq3638 y X0
       grind)
    | exact resolve eq3638 eq228513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3638
  have eq228787 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (M.op X1 X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq2643 X0 X1 y
       have i₂ := eq228513 (M.op X0 X0)
       grind)
    | exact superpose eq228513 eq2643
    | exact resolve eq2643 eq228513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2643 eq228513
  have eq228873 : ∀ X0 : G, (M.op X0 X0) = (τ y) := by
    intro X0
    first
    | (have j0 := eq228771 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228771
  have eq228875 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq228765 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228765
  have eq228877 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq228760 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228760
  have eq228878 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq228759
  have eq228940 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k (M.op X1 X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq228787 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq228787
    | (have j0 := eq228787 X0 X1
       grind)
    | exact resolve eq228787 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228787
  have eq228952 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq228877 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq228877
    | (have j0 := eq228877 X0
       grind)
    | exact resolve eq228877 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228877
  have eq228953 : (σ y) = (τ y) := by
    first
    | (have i₁ := eq228878
       have i₂ := eq228873 (σ y)
       grind)
    | exact superpose eq228873 eq228878
    | exact resolve eq228878 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228878
  have eq229000 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (τ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq228940 X0 x
       have i₂ := eq228873 x
       grind)
    | exact superpose eq228873 eq228940
    | exact resolve eq228940 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228940
  have eq229002 : (σ y) = (τ y) := by
    first
    | (have i₁ := eq228953
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq228953
    | exact resolve eq228953 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228953
  have eq229015 : ∀ X0 : G, (σ (M.op X0 X0)) = (τ y) := by
    intro X0
    first
    | exact superpose eq228952 eq229000
    | exact resolve eq229000 eq228952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228952 eq229000
  have eq229022 : ∀ X0 : G, (σ y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq229015 X0
       have i₂ := eq229002
       grind)
    | exact superpose eq229002 eq229015
    | exact resolve eq229015 eq229002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229015
  have eq229026 : (σ y) = (σ (τ y)) := by
    first
    | (have i₁ := eq229022 x
       have i₂ := eq228873 x
       grind)
    | exact superpose eq228873 eq229022
    | exact resolve eq229022 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229022
  have eq229027 : y = (σ y) := by
    first
    | (have i₁ := eq229026
       have i₂ := eq14 y
       grind)
    | exact superpose eq14 eq229026
    | exact resolve eq229026 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229026
  have eq229028 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq229027
       grind)
    | exact superpose eq229027 eq18
    | exact resolve eq18 eq229027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq229029 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq229027
       grind)
    | exact superpose eq229027 eq24
    | exact resolve eq24 eq229027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq229032 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) (σ y)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq229027
       grind)
    | exact superpose eq229027 eq176
    | exact resolve eq176 eq229027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq229118 : x = (M.op (M.op (τ y) (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq229032 x
       have i₂ := eq228873 x
       grind)
    | exact superpose eq228873 eq229032
    | exact resolve eq229032 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229032
  have eq229139 : x = (M.op (M.op (σ y) (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq229118
       have i₂ := eq229002
       grind)
    | exact superpose eq229002 eq229118
    | exact resolve eq229118 eq229002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229118
  have eq229150 : x = (M.op (τ y) (M.op x y)) := by
    first
    | (have i₁ := eq229139
       have i₂ := eq228873 sF3
       grind)
    | exact superpose eq228873 eq229139
    | exact resolve eq229139 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229139
  have eq229161 : x = (M.op (σ y) (M.op x y)) := by
    first
    | (have i₁ := eq229150
       have i₂ := eq229002
       grind)
    | exact superpose eq229002 eq229150
    | exact resolve eq229150 eq229002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229150
  have eq232422 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X1) y) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq756 X0 X0 X0
       have i₂ := eq228875 X0
       grind)
    | exact superpose eq228875 eq756
    | (have j0 := eq756 X0 X1 x
       grind)
    | exact resolve eq756 eq228875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq228875
  have eq232698 : ∀ X0 X1 : G, (M.op (k (M.op X0 X0) X1) (σ y)) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq232422 X0 X1
       have i₂ := eq229027
       grind)
    | exact superpose eq229027 eq232422
    | (have j0 := eq232422 X0 X1
       grind)
    | exact resolve eq232422 eq229027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232422
  have eq233523 : ∀ X0 X1 : G, (M.op (k (τ y) X1) (σ y)) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq232698 X0 X1
       have i₂ := eq228873 X0
       grind)
    | exact superpose eq228873 eq232698
    | (have j0 := eq232698 X0 X1
       grind)
    | exact resolve eq232698 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232698
  have eq234279 : ∀ X0 X1 : G, (M.op (k (σ y) X1) (σ y)) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X1 ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq233523 X0 X1
       have i₂ := eq229002
       grind)
    | exact superpose eq229002 eq233523
    | (have j0 := eq233523 X0 X1
       grind)
    | exact resolve eq233523 eq229002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233523
  have eq234924 : ∀ X1 : G, (τ y) = X1 ∨ (M.op (k (σ y) X1) (σ y)) = X1 ∨ y = X1 := by
    intro X1
    first
    | (have i₁ := eq234279 x X1
       have i₂ := eq228873 (M.op x x)
       grind)
    | exact superpose eq228873 eq234279
    | (have j0 := eq234279 x X1
       grind)
    | exact resolve eq234279 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234279
  have eq235360 : ∀ X1 : G, (σ y) = X1 ∨ (M.op (k (σ y) X1) (σ y)) = X1 ∨ y = X1 := by
    intro X1
    first
    | (have i₁ := eq234924 X1
       have i₂ := eq229002
       grind)
    | exact superpose eq229002 eq234924
    | (have j0 := eq234924 X1
       grind)
    | exact resolve eq234924 eq229002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234924
  have eq235628 : ∀ X1 : G, (σ y) = X1 ∨ (σ y) = X1 ∨ (M.op (k (σ y) X1) (σ y)) = X1 := by
    intro X1
    first
    | (have i₁ := eq235360 X1
       have i₂ := eq229027
       grind)
    | exact superpose eq229027 eq235360
    | (have j0 := eq235360 X1
       grind)
    | exact resolve eq235360 eq229027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235360
  have eq235629 : ∀ X1 : G, (M.op (k (σ y) X1) (σ y)) = X1 ∨ (σ y) = X1 := by
    intro X1
    first
    | (have j0 := eq235628 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235628
  have eq240249 : ∀ X0 : G, x = (k (M.op (M.op X0 X0) (σ y)) (M.op x y)) ∨ (M.op X0 X0) = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq229028 eq792
    | (have j0 := eq792 X0 y x
       grind)
    | exact resolve eq792 eq229028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq229028
  have eq240262 : ∀ X0 : G, x = (k (M.op (M.op X0 X0) (σ y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq240249 X0
       have j1 := eq2325 X0 (M.op x y)
       grind)
    | (have r₁ := eq240249 X0
       have r₂ := eq2325 X0 (M.op x y)
       grind)
    | (have r₁ := eq240249 X0
       have r₂ := eq2325 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq240249 eq2325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325 eq240249
  have eq240274 : x = (k (M.op (τ y) (σ y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq240262 x
       have i₂ := eq228873 x
       grind)
    | exact superpose eq228873 eq240262
    | exact resolve eq240262 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240262
  have eq240284 : x = (k (M.op (σ y) (σ y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq240274
       have i₂ := eq229002
       grind)
    | exact superpose eq229002 eq240274
    | exact resolve eq240274 eq229002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240274
  have eq240293 : x = (k (τ y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq240284
       have i₂ := eq228873 sF3
       grind)
    | exact superpose eq228873 eq240284
    | exact resolve eq240284 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240284
  have eq240302 : x = (k (σ y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq240293
       have i₂ := eq229002
       grind)
    | exact superpose eq229002 eq240293
    | exact resolve eq240293 eq229002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240293
  have eq240308 : (M.op x y) = (τ y) ∨ x = (k (σ y) (M.op x y)) := by
    first
    | (have i₁ := eq240302
       have i₂ := eq228873 sF0
       grind)
    | exact superpose eq228873 eq240302
    | exact resolve eq240302 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240302
  have eq240310 : x = (k (σ y) (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq240308
       have i₂ := eq229002
       grind)
    | exact superpose eq229002 eq240308
    | exact resolve eq240308 eq229002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240308
  have eq248505 : (σ x) = (k (σ (σ y)) (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq240310 eq41
    | exact resolve eq41 eq240310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq240310
  have eq248508 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq229029 eq248505
    | exact resolve eq248505 eq229029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248505
  have eq248511 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq248508
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq248508
    | exact resolve eq248508 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248508
  have eq280356 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq248511 eq235629
    | (have j0 := eq235629 (σ (M.op x y))
       grind)
    | exact resolve eq235629 eq248511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235629 eq248511
  have eq280501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26 eq280356
    | exact resolve eq280356 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280356
  have eq280552 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq280501
       have r₂ := eq27
       grind)
    | exact resolve eq280501 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280501
  have eq280625 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq280552 eq28
    | exact resolve eq28 eq280552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq280552
  have eq280779 : y = (M.op x y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq31 eq280625
    | exact resolve eq280625 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq280625
  have eq280830 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq280779
       have i₂ := eq229027
       grind)
    | exact superpose eq229027 eq280779
    | exact resolve eq280779 eq229027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229027 eq280779
  have eq280831 : (M.op x y) = (σ y) := by grind
  clear eq280830
  have eq280990 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq280831 eq229029
    | exact resolve eq229029 eq280831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229029
  have eq280992 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq280831 eq229161
    | exact resolve eq229161 eq280831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229161
  have eq281008 : x = (τ y) := by
    first
    | (have i₁ := eq280992
       have i₂ := eq228873 sF0
       grind)
    | exact superpose eq228873 eq280992
    | exact resolve eq280992 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280992
  have eq281097 : x = (σ y) := by
    first
    | (have i₁ := eq281008
       have i₂ := eq229002
       grind)
    | exact superpose eq229002 eq281008
    | exact resolve eq281008 eq229002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281008
  have eq281166 : x = (M.op x y) := by
    first
    | exact superpose eq280831 eq281097
    | exact resolve eq281097 eq280831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281097
  have eq281562 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq281166
       grind)
    | exact superpose eq281166 eq22
    | exact resolve eq22 eq281166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq281166
  have eq281684 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq280990 eq281562
    | exact resolve eq281562 eq280990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281562
  have eq281792 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq281684 eq26
    | exact resolve eq26 eq281684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq281684
  have eq281944 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq280831 eq281792
    | exact resolve eq281792 eq280831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281792
  have eq281997 : (M.op (σ x) (σ y)) = (τ y) := by
    first
    | (have i₁ := eq281944
       have i₂ := eq228873 sF0
       grind)
    | exact superpose eq228873 eq281944
    | exact resolve eq281944 eq228873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228873 eq281944
  have eq282044 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq281997
       have i₂ := eq229002
       grind)
    | exact superpose eq229002 eq281997
    | exact resolve eq281997 eq229002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229002 eq281997
  have eq282077 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq280831 eq282044
    | exact resolve eq282044 eq280831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280831 eq282044
  have eq282112 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq282077 eq27
    | exact resolve eq27 eq282077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq282077
  have eq282328 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq280990 eq20
    | exact resolve eq20 eq280990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq280990
  have eq282475 : False := by grind
  exact eq282475

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_x_pyx_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq9 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq40
    | exact resolve eq40 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq40 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq40 eq40
    | exact resolve eq40 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
       have i₂ := eq40 X2 X3 X0
       grind)
    | exact superpose eq40 eq9
    | exact resolve eq9 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq12 X2 X1
       have i₂ := eq69 X1 X0
       grind)
    | exact superpose eq69 eq12
    | (have j0 := eq12 X2 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq69 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq69 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (M.op X0 X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 (M.op X1 X1) X1 X2
       have i₂ := eq69 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq40 (M.op X1 X1) X1 X2
       have i₂ := eq69 (M.op X1 X1) X0
       grind)
    | exact superpose eq69 eq40
    | exact resolve eq40 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq40 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq69 X2 (M.op X1 (M.op X0 X0))
       grind)
    | (have i₁ := eq40 X1 X0 (M.op X1 (M.op X0 X0))
       have i₂ := eq69 (M.op X1 (M.op X0 X0)) X2
       grind)
    | exact superpose eq69 eq40
    | exact resolve eq40 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq69 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq69 X0 X1
       grind)
    | exact superpose eq69 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq69 X0 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq69 X1 X1
       grind)
    | exact resolve eq13 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq113 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 X1)
       have i₂ := eq97 (σ X0) X1
       grind)
    | exact superpose eq97 eq28
    | exact resolve eq28 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq114 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (M.op X1 X1)
       have i₂ := eq97 (τ X0) X1
       grind)
    | exact superpose eq97 eq17
    | exact resolve eq17 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq115 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq114
    | exact resolve eq114 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq113
    | exact resolve eq113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq161 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq227 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op X1 X1)) ≠ X2 ∨ (k X3 X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X2
       have i₂ := eq68 X2 X0 X1
       grind)
    | (have i₁ := eq12 X0 (M.op X2 X2)
       have i₂ := eq68 X0 X2 X2
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 X3 X2
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 X1) (M.op X2 X2))
       have r₂ := eq68 (M.op (M.op X1 X1) (M.op X2 X2)) X1 X2
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq68 X0 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq485 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq104 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq104
    | (have j0 := eq104 (σ X0)
       grind)
    | exact resolve eq104 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq503 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq104 (τ X0)
       grind)
    | exact superpose eq104 eq18
    | (have j1 := eq104 (τ X0)
       grind)
    | exact resolve eq18 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq521 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq503 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq503
    | (have j0 := eq503 X0
       grind)
    | exact resolve eq503 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq531 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) = (M.op (M.op (M.op X4 X4) (M.op X5 X3)) X5) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq41 X5 X4 X3 x
       have i₂ := eq68 x X0 X1
       grind)
    | (have i₁ := eq41 X0 X1 x (M.op x x)
       have i₂ := eq68 X0 x x
       grind)
    | exact superpose eq68 eq41
    | exact resolve eq41 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 X2)) = (M.op (M.op (M.op X3 X3) X0) (M.op (M.op X4 X4) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq41 (M.op (M.op X4 X4) X2) X3 (M.op X0 X2) X1
       have i₂ := eq9 X0 X4 X2
       grind)
    | exact superpose eq9 eq41
    | exact resolve eq41 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq41 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
       have i₂ := eq40 X2 X3 X0
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1) (M.op X4 X2)) = X4 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq9 X4 x X2
       have i₂ := eq41 X1 X0 X2 x
       grind)
    | (have i₁ := eq9 X0 (M.op X2 X2) X2
       have i₂ := eq41 X2 X2 X2 x
       grind)
    | exact superpose eq41 eq9
    | exact resolve eq9 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X4) = (M.op (M.op (M.op X3 X3) X2) (M.op (M.op (M.op X0 X0) (M.op X1 X2)) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X4) X3 X2
       have i₂ := eq41 X1 X0 X2 X4
       grind)
    | (have i₁ := eq9 (M.op (M.op X1 X1) (M.op X0 X2)) X1 X0
       have i₂ := eq41 X0 X1 X2 X3
       grind)
    | exact superpose eq41 eq9
    | exact resolve eq9 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq161 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq161 X0 X1
       grind)
    | exact superpose eq161 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq161 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq161 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq161 X0 X1
       grind)
    | exact resolve eq13 eq161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq855 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq850 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq856 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq855 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq861 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq856 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq856
    | (have j0 := eq856 X0 X1
       grind)
    | exact resolve eq856 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856
  have eq862 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq861 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq1140 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq115 (σ (M.op X1 X1)) X1
       have i₂ := eq105 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq105 eq115
    | (have j1 := eq105 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq115 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1145 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq116 (τ (M.op X1 X1)) X1
       have i₂ := eq105 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq105 eq116
    | (have j1 := eq105 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq116 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1149 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq105 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq1153 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1145 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1145
  have eq1157 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1140 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1224 : ∀ X0 X2 X3 : G, (M.op (τ (M.op X0 X0)) (M.op X2 (M.op X3 X3))) = X2 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq82 X3 x X2
       have i₂ := eq1153 x X0
       grind)
    | exact superpose eq1153 eq82
    | exact resolve eq82 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1271 : ∀ X0 X1 X2 : G, (τ (k (M.op X1 X1) X2)) = (k (M.op X0 X0) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (M.op X1 X1)
       have i₂ := eq1153 X0 X1
       grind)
    | exact superpose eq1153 eq31
    | exact resolve eq31 eq1153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3000 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X3 (M.op X4 (M.op X5 X5)))) X3) = X4 := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq70 X3 x X4 X5
       have i₂ := eq68 x X0 X1
       grind)
    | (have i₁ := eq70 X0 (M.op x x) x X3
       have i₂ := eq68 X0 x x
       grind)
    | exact superpose eq68 eq70
    | exact resolve eq70 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq3134 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op (M.op X1 (M.op X3 X3)) (M.op X0 (M.op X4 X4)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq40 X1 X3 (M.op (M.op X2 X2) (M.op (M.op X1 (M.op X3 X3)) (M.op X0 (M.op X4 X4))))
       have i₂ := eq70 (M.op X1 (M.op X3 X3)) X2 X0 X4
       grind)
    | exact superpose eq70 eq40
    | exact resolve eq40 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3484 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X2 X2) X3)) (M.op X4 (M.op X0 X3))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq589 X1 (M.op (M.op X2 X2) X3) (M.op X0 X3) X4
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq589
    | exact resolve eq589 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3515 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 X3))) X1) X2) (M.op X5 X3)) = X5 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq589 x X2 X3 X5
       have i₂ := eq41 X1 X0 (M.op X2 X3) x
       grind)
    | (have i₁ := eq589 (M.op (M.op X1 X2) (M.op X1 X2)) X1 X2 x
       have i₂ := eq41 (M.op X1 X2) (M.op X1 X2) (M.op X1 X2) X3
       grind)
    | exact superpose eq41 eq589
    | exact resolve eq589 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq589
  have eq3746 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq69 X1 (σ X0)
       have i₂ := eq485 X0
       grind)
    | exact superpose eq485 eq69
    | (have j1 := eq485 X0
       grind)
    | exact resolve eq69 eq485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq485
  have eq5111 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq521 X0
       grind)
    | exact superpose eq521 eq10
    | (have j1 := eq521 X0
       grind)
    | exact resolve eq10 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq5510 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq862 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq862
    | exact resolve eq862 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5531 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq862 x y
       grind)
    | exact superpose eq862 eq16
    | (have j1 := eq862 x y
       grind)
    | exact resolve eq16 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5617 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op X2 X2) (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 (σ X1)
       have i₂ := eq862 X0 X1
       grind)
    | exact superpose eq862 eq9
    | (have j1 := eq862 X0 X1
       grind)
    | exact resolve eq9 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5656 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5510 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq5510
    | (have j0 := eq5510 X0 X1
       grind)
    | exact resolve eq5510 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5510
  have eq6511 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X2 X2) (M.op X3 (M.op X4 X4)))) X1) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq70 X1 x X3 X4
       have i₂ := eq557 X1 x (M.op X3 (M.op X4 X4)) X0 X2
       grind)
    | (have i₁ := eq70 (M.op X4 X4) (M.op X3 X3) X2 X3
       have i₂ := eq557 (M.op X3 X3) X1 (M.op X2 (M.op X3 X3)) X3 X4
       grind)
    | exact superpose eq557 eq70
    | exact resolve eq70 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6918 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X3) X1) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6511 X0 X1 x X3 x
       have i₂ := eq82 x x X3
       grind)
    | exact superpose eq82 eq6511
    | exact resolve eq6511 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq6511
  have eq7043 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6918 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1))) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq70 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)) X0 X1
       grind)
    | exact superpose eq70 eq6918
    | exact resolve eq6918 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq6918
  have eq7213 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7043 X1 x X2
       have i₂ := eq1157 x X0
       grind)
    | exact superpose eq1157 eq7043
    | exact resolve eq7043 eq1157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7716 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X2 (M.op (M.op X0 X2) (M.op X3 X3)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq561 X2 X1 (M.op X0 X2) X3 x
       have i₂ := eq9 X0 x X2
       grind)
    | exact superpose eq9 eq561
    | exact resolve eq561 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7753 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X3 X3) (M.op X4 (M.op X1 (M.op X2 (M.op X5 X5))))) = (M.op (M.op (M.op X6 X6) X4) (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq557 X4 X3 (M.op X1 (M.op X2 (M.op X5 X5))) X6 x
       have i₂ := eq561 X1 x X2 X5 X0
       grind)
    | exact superpose eq561 eq557
    | exact resolve eq557 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq561
  have eq9271 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op (M.op (M.op X3 X3) (σ X1)) (M.op (M.op (M.op X4 X4) (σ (k X0 X1))) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq618 X4 (σ X0) (σ X1) X3 X2
       have i₂ := eq862 X0 X1
       grind)
    | exact superpose eq862 eq618
    | (have j1 := eq862 X0 X1
       grind)
    | exact resolve eq618 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq862
  have eq42841 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5656 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5656
    | (have j0 := eq5656 X1 X1
       grind)
    | exact resolve eq5656 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5656
  have eq145384 : ∀ X0 X1 X2 : G, (k X1 (τ (σ X0))) = X1 ∨ (M.op X2 X2) = (σ (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq116 X1 (σ X0)
       have i₂ := eq3746 X0 X2
       grind)
    | exact superpose eq3746 eq116
    | (have j1 := eq3746 X0 X2
       grind)
    | exact resolve eq116 eq3746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3746
  have eq145958 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (k X0 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq145384 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq145384
    | (have j0 := eq145384 X0 X1 X2
       grind)
    | exact resolve eq145384 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145384
  have eq146319 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (τ (σ (k X0 X0))) ∨ (k X3 X0) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1153 X1 x
       have i₂ := eq145958 X0 X3 x
       grind)
    | exact superpose eq145958 eq1153
    | (have j1 := eq145958 X0 X3 x
       grind)
    | exact resolve eq1153 eq145958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1153 eq145958
  have eq147130 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (k X0 X0) ∨ (k X3 X0) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq146319 X0 X1 X3
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq146319
    | (have j0 := eq146319 X0 X1 X3
       grind)
    | exact resolve eq146319 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146319
  have eq152339 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5531
       have i₂ := eq42841 x y
       grind)
    | exact superpose eq42841 eq5531
    | (have j1 := eq42841 x (σ y)
       grind)
    | exact resolve eq5531 eq42841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5531 eq42841
  have eq152342 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq152339
  have eq152383 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq116 X0 (σ y)
       have i₂ := eq152342
       grind)
    | exact superpose eq152342 eq116
    | exact resolve eq116 eq152342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq152342
  have eq152887 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq152383 X0
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq152383
    | exact resolve eq152383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152383
  have eq152891 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq152887 X0
       have j1 := eq12 X0 y
       grind)
    | (have r₁ := eq152887 X0
       have r₂ := eq12 X0 y
       grind)
    | exact resolve eq152887 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152887
  have eq152914 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1149 X0 y
       have i₂ := eq152891 y
       grind)
    | exact superpose eq152891 eq1149
    | (have j0 := eq1149 X0 y
       grind)
    | (have r₁ := eq1149 X0 y
       have r₂ := eq152891 y
       grind)
    | exact resolve eq1149 eq152891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1149 eq152891
  have eq152973 : ∀ X0 : G, y = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq152914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152914
  have eq153301 : ∀ X0 X1 : G, (τ (k (M.op X0 X0) X1)) = (k y (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1271 x X0 X1
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq1271
    | exact resolve eq1271 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq153797 : ∀ X1 : G, y = (σ (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq7213 X1 x (σ (M.op X1 X1))
       have i₂ := eq152973 (M.op x (σ (M.op X1 X1)))
       grind)
    | exact superpose eq152973 eq7213
    | exact resolve eq7213 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7213
  have eq153960 : y = (σ y) := by
    first
    | (have i₁ := eq153797 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq153797
    | exact resolve eq153797 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153797
  have eq154368 : ∀ X1 : G, (k y (τ X1)) = (τ (k y X1)) := by
    intro X1
    first
    | (have i₁ := eq153301 x X1
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq153301
    | exact resolve eq153301 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153301
  have eq155128 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq153960
       grind)
    | exact superpose eq153960 eq16
    | exact resolve eq16 eq153960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155679 : ∀ X0 : G, y = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq5111 X0
       have i₂ := eq152973 (τ X0)
       grind)
    | exact superpose eq152973 eq5111
    | (have j0 := eq5111 X0
       grind)
    | exact resolve eq5111 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5111
  have eq155680 : ∀ X0 : G, y = (τ (k X0 X0)) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq155679 X0
       have i₂ := eq152973 (τ X0)
       grind)
    | exact superpose eq152973 eq155679
    | (have j0 := eq155679 X0
       grind)
    | exact resolve eq155679 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155679
  have eq155745 : ∀ X0 : G, y = (τ (τ (k X0 X0))) ∨ y = (τ (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq155680 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq155680
    | (have j0 := eq155680 (τ (k X0 X0))
       grind)
    | exact resolve eq155680 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155680
  have eq156046 : ∀ X0 X1 X3 X5 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X3) = (M.op (M.op y (M.op X5 X3)) X5) := by
    intro X0 X1 X3 X5
    first
    | (have i₁ := eq531 X0 X1 X3 x X5
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq531
    | exact resolve eq531 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq156047 : ∀ X0 X3 X5 : G, (M.op (M.op y (M.op X5 X3)) X5) = (M.op (M.op (M.op X0 X0) y) X3) := by
    intro X0 X3 X5
    first
    | (have i₁ := eq156046 X0 x X3 X5
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq156046
    | exact resolve eq156046 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156046
  have eq156048 : ∀ X3 X5 : G, (M.op (M.op y (M.op X5 X3)) X5) = (M.op (M.op y y) X3) := by
    intro X3 X5
    first
    | (have i₁ := eq156047 x X3 X5
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq156047
    | exact resolve eq156047 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156047
  have eq156049 : ∀ X3 X5 : G, (M.op y X3) = (M.op (M.op y (M.op X5 X3)) X5) := by
    intro X3 X5
    first
    | (have i₁ := eq156048 X3 X5
       have i₂ := eq152973 y
       grind)
    | exact superpose eq152973 eq156048
    | exact resolve eq156048 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156048
  have eq157542 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op X3 (M.op X4 y))) X3) = X4 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq3000 X0 X1 X3 X4 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq3000
    | exact resolve eq3000 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3000
  have eq157543 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) y) (M.op X3 (M.op X4 y))) X3) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq157542 X0 x X3 X4
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq157542
    | exact resolve eq157542 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157542
  have eq157544 : ∀ X3 X4 : G, (M.op (M.op (M.op y y) (M.op X3 (M.op X4 y))) X3) = X4 := by
    intro X3 X4
    first
    | (have i₁ := eq157543 x X3 X4
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq157543
    | exact resolve eq157543 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157543
  have eq157545 : ∀ X3 X4 : G, (M.op (M.op y (M.op X3 (M.op X4 y))) X3) = X4 := by
    intro X3 X4
    first
    | (have i₁ := eq157544 X3 X4
       have i₂ := eq152973 y
       grind)
    | exact superpose eq152973 eq157544
    | exact resolve eq157544 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157544
  have eq157546 : ∀ X4 : G, (M.op y (M.op X4 y)) = X4 := by
    intro X4
    first
    | (have i₁ := eq157545 x X4
       have i₂ := eq156049 (M.op X4 y) x
       grind)
    | exact superpose eq156049 eq157545
    | exact resolve eq157545 eq156049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157545
  have eq157652 : ∀ X0 : G, (M.op (M.op y X0) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq156049 (M.op x y) y
       have i₂ := eq157546 x
       grind)
    | exact superpose eq157546 eq156049
    | exact resolve eq156049 eq157546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157978 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op (M.op X1 (M.op X3 X3)) (M.op X0 y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3134 X0 X1 X2 X3 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq3134
    | exact resolve eq3134 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3134
  have eq157979 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op (M.op X1 y) (M.op X0 y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq157978 X0 X1 X2 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq157978
    | exact resolve eq157978 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157978
  have eq157980 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op X1 y) (M.op X0 y))) := by
    intro X0 X1
    first
    | (have i₁ := eq157979 X0 X1 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq157979
    | exact resolve eq157979 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157979
  have eq158480 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 y)) = (M.op y (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq156049 (M.op X1 y) (M.op X0 y)
       have i₂ := eq157980 X1 X0
       grind)
    | exact superpose eq157980 eq156049
    | exact resolve eq156049 eq157980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157980
  have eq158633 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq158480 X0 X1
       have i₂ := eq157546 X1
       grind)
    | (have i₁ := eq158480 X0 X1
       have i₂ := eq157546 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq157546 eq158480
    | exact resolve eq158480 eq157546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158480
  have eq159251 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X1) X0) (M.op y X3)) (M.op X4 (M.op X0 X3))) = X4 := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq3484 X0 X1 x X3 X4
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq3484
    | exact resolve eq3484 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3484
  have eq159252 : ∀ X0 X3 X4 : G, (M.op (M.op (M.op y X0) (M.op y X3)) (M.op X4 (M.op X0 X3))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq159251 X0 x X3 X4
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq159251
    | exact resolve eq159251 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159251
  have eq159490 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op y X0) (M.op y (M.op X2 X2))) (M.op X3 (M.op X0 (M.op X1 X1)))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq159252 X0 (M.op X2 X2) X3
       have i₂ := eq83 X1 X0 X2
       grind)
    | (have i₁ := eq159252 X0 (M.op X2 X2) X3
       have i₂ := eq83 X2 X0 X1
       grind)
    | exact superpose eq83 eq159252
    | exact resolve eq159252 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159592 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op y X0) (M.op y (M.op X1 (M.op X2 X2)))) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq159252 X0 (M.op X1 (M.op X2 X2)) X1
       have i₂ := eq40 X1 X2 X0
       grind)
    | exact superpose eq40 eq159252
    | exact resolve eq159252 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159252
  have eq160732 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) (M.op y (M.op X1 y))) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq159592 X0 X1 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq159592
    | exact resolve eq159592 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159592
  have eq160828 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op y X0) (M.op y (M.op X2 X2))) (M.op X3 (M.op X0 y))) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq159490 X0 x X2 X3
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq159490
    | exact resolve eq159490 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159490
  have eq161176 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq160732 X0 X1
       have i₂ := eq157546 X1
       grind)
    | (have i₁ := eq160732 X0 X1
       have i₂ := eq157546 (M.op y (M.op X1 y))
       grind)
    | exact superpose eq157546 eq160732
    | exact resolve eq160732 eq157546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157546 eq160732
  have eq161257 : ∀ X0 X3 : G, (M.op X0 (M.op X3 (M.op X0 y))) = X3 := by
    intro X0 X3
    first
    | (have i₁ := eq160828 X0 x X3
       have i₂ := eq7043 y x X0
       grind)
    | exact superpose eq7043 eq160828
    | exact resolve eq160828 eq7043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7043 eq160828
  have eq164813 : ∀ X1 X2 X3 X5 : G, (M.op (M.op (M.op (M.op y (M.op X1 (M.op X2 X3))) X1) X2) (M.op X5 X3)) = X5 := by
    intro X1 X2 X3 X5
    first
    | (have i₁ := eq3515 x X1 X2 X3 X5
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq3515
    | exact resolve eq3515 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3515
  have eq164814 : ∀ X2 X3 X5 : G, (M.op (M.op (M.op y (M.op X2 X3)) X2) (M.op X5 X3)) = X5 := by
    intro X2 X3 X5
    first
    | (have i₁ := eq164813 x X2 X3 X5
       have i₂ := eq156049 (M.op X2 X3) x
       grind)
    | exact superpose eq156049 eq164813
    | exact resolve eq164813 eq156049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164813
  have eq164815 : ∀ X3 X5 : G, (M.op (M.op y X3) (M.op X5 X3)) = X5 := by
    intro X3 X5
    first
    | (have i₁ := eq164814 x X3 X5
       have i₂ := eq156049 X3 x
       grind)
    | exact superpose eq156049 eq164814
    | exact resolve eq164814 eq156049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156049 eq164814
  have eq165127 : ∀ X0 X1 : G, y ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq227 y y X0 X1
       have i₂ := eq164815 y y
       grind)
    | exact superpose eq164815 eq227
    | (have j0 := eq227 X0 X1 X0 X1
       grind)
    | (have r₁ := eq227 y y y x
       have r₂ := eq164815 y y
       grind)
    | (have r₁ := eq227 X0 X1 (M.op (M.op y x) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) x)) x
       have r₂ := eq164815 x (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact resolve eq227 eq164815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq165619 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op (M.op X2 X1) y))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7716 X2 X0 X1 (M.op y x)
       have i₂ := eq164815 x y
       grind)
    | exact superpose eq164815 eq7716
    | exact resolve eq7716 eq164815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7716 eq164815
  have eq165905 : ∀ X1 X2 : G, (M.op y (M.op X1 (M.op (M.op X2 X1) y))) = X2 := by
    intro X1 X2
    first
    | (have i₁ := eq165619 x X1 X2
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq165619
    | exact resolve eq165619 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165619
  have eq169715 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 (M.op (M.op X1 X0) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq158633 (M.op X1 X0) (M.op X1 y)
       have i₂ := eq158633 X1 X0
       grind)
    | exact superpose eq158633 eq158633
    | exact resolve eq158633 eq158633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158633
  have eq244136 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op y (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5617 X0 X1 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq5617
    | (have j0 := eq5617 X0 X1 x
       grind)
    | exact resolve eq5617 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5617
  have eq244137 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op y (σ X1)) (σ (k X0 X1))) ∨ (σ X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq244136 X0 X1
       have i₂ := eq152973 (σ X1)
       grind)
    | exact superpose eq152973 eq244136
    | (have j0 := eq244136 X0 X1
       grind)
    | exact resolve eq244136 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244136
  have eq244927 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op y (σ (τ X1))) (σ (τ (k X0 X1)))) ∨ y = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq244137 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq244137
    | (have j0 := eq244137 X0 (τ X1)
       grind)
    | exact resolve eq244137 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq244137
  have eq245067 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op y (σ (τ X1))) (k X0 X1)) ∨ y = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq244927 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq244927
    | (have j0 := eq244927 X0 X1
       grind)
    | exact resolve eq244927 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244927
  have eq245230 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op y X1) (k X0 X1)) ∨ y = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq245067 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq245067
    | (have j0 := eq245067 X0 X1
       grind)
    | exact resolve eq245067 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245067
  have eq245363 : ∀ X0 X1 : G, (M.op (M.op y X1) (k X0 X1)) = X0 ∨ y = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq245230 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq245230
    | (have j0 := eq245230 X0 X1
       grind)
    | exact resolve eq245230 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245230
  have eq245463 : ∀ X0 X1 : G, (M.op (M.op y X1) (k X0 X1)) = X0 ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq245363 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq245363
    | (have j0 := eq245363 X0 X1
       grind)
    | exact resolve eq245363 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245363
  have eq245982 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq161176 X1 (k X0 X1)
       have i₂ := eq245463 X0 X1
       grind)
    | exact superpose eq245463 eq161176
    | (have j1 := eq245463 X0 X1
       grind)
    | exact resolve eq161176 eq245463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161176
  have eq246027 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op (k X0 X1) (M.op X0 y)) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq169715 (k X0 X1) (M.op y X1)
       have i₂ := eq245463 X0 X1
       grind)
    | exact superpose eq245463 eq169715
    | (have j1 := eq245463 X0 X1
       grind)
    | exact resolve eq169715 eq245463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169715 eq245463
  have eq246033 : ∀ X0 X1 : G, (M.op (k X0 X1) (M.op X0 y)) = X1 ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq246027 X0 X1
       have i₂ := eq157652 X1
       grind)
    | exact superpose eq157652 eq246027
    | (have j0 := eq246027 X0 X1
       grind)
    | exact resolve eq246027 eq157652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246027
  have eq246908 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ y = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq245982 (τ X0) X1
       grind)
    | exact superpose eq245982 eq17
    | (have j1 := eq245982 X0 X1
       grind)
    | exact resolve eq17 eq245982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq245982
  have eq247843 : ∀ X0 X1 : G, (M.op (k y X0) (M.op X1 X1)) = X0 ∨ y = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq83 y (k y X0) X1
       have i₂ := eq246033 y X0
       grind)
    | exact superpose eq246033 eq83
    | (have j1 := eq246033 X0 X0
       grind)
    | exact resolve eq83 eq246033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq247976 : ∀ X0 : G, (M.op (k y X0) y) = X0 ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq247843 X0 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq247843
    | (have j0 := eq247843 X0 x
       grind)
    | exact resolve eq247843 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247843
  have eq248640 : ∀ X0 X1 : G, (M.op (k (k y X0) X1) X0) = X1 ∨ y = X1 ∨ y = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq246033 (k y X0) X1
       have i₂ := eq247976 X0
       grind)
    | exact superpose eq247976 eq246033
    | (have j0 := eq246033 X0 X1
       have j1 := eq247976 X1
       grind)
    | exact resolve eq246033 eq247976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246033 eq247976
  have eq301003 : ∀ X0 X1 X2 : G, (σ X0) = (k (M.op X1 X1) (σ (M.op X0 (M.op X2 X2)))) ∨ y = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq246908 (M.op X1 X1) (M.op X0 (M.op X2 X2))
       have i₂ := eq1224 X1 X0 X2
       grind)
    | exact superpose eq1224 eq246908
    | (have j0 := eq246908 X0 (M.op X0 (M.op X2 X2))
       grind)
    | exact resolve eq246908 eq1224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq246908
  have eq301341 : ∀ X0 X1 X2 : G, (σ X0) = (k (M.op X1 X1) (σ (M.op X0 y))) ∨ y = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq301003 X0 X1 X2
       have i₂ := eq152973 X2
       grind)
    | exact superpose eq152973 eq301003
    | (have j0 := eq301003 X0 X1 X2
       grind)
    | exact resolve eq301003 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301003
  have eq301557 : ∀ X0 X2 : G, (σ X0) = (k y (σ (M.op X0 y))) ∨ y = (M.op X0 (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq301341 X0 x X2
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq301341
    | (have j0 := eq301341 X0 x X2
       grind)
    | exact resolve eq301341 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301341
  have eq301732 : ∀ X0 : G, (σ X0) = (k y (σ (M.op X0 y))) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq301557 X0 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq301557
    | (have j0 := eq301557 X0 x
       grind)
    | exact resolve eq301557 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301557
  have eq430107 : ∀ X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X3 X3) (M.op X4 (M.op X1 (M.op X2 (M.op X5 X5))))) = (M.op (M.op (M.op X6 X6) X4) (M.op (M.op y X1) X2)) := by
    intro X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq7753 x X1 X2 X3 X4 X5 X6
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq7753
    | exact resolve eq7753 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7753
  have eq430108 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op X4 (M.op X1 (M.op X2 (M.op X5 X5))))) = (M.op (M.op y X4) (M.op (M.op y X1) X2)) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq430107 X1 X2 X3 X4 X5 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq430107
    | exact resolve eq430107 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430107
  have eq430109 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op X4 (M.op X1 (M.op X2 y)))) = (M.op (M.op y X4) (M.op (M.op y X1) X2)) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq430108 X1 X2 X3 X4 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq430108
    | exact resolve eq430108 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430108
  have eq430110 : ∀ X1 X2 X4 : G, (M.op y (M.op X4 (M.op X1 (M.op X2 y)))) = (M.op (M.op y X4) (M.op (M.op y X1) X2)) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq430109 X1 X2 x X4
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq430109
    | exact resolve eq430109 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430109
  have eq624703 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) = (M.op (M.op (M.op X3 X3) (σ X1)) (M.op (M.op y (σ (k X0 X1))) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9271 X0 X1 X2 X3 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq9271
    | (have j0 := eq9271 X0 X1 X2 X3 x
       grind)
    | exact resolve eq9271 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9271
  have eq624704 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op y (σ X1)) (M.op (M.op y (σ (k X0 X1))) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq624703 X0 X1 X2 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq624703
    | (have j0 := eq624703 X0 X1 X2 x
       grind)
    | exact resolve eq624703 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624703
  have eq624705 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op y (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op (σ X0) y)))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq624704 X0 X1 X2
       have i₂ := eq430110 (σ (k X0 X1)) (σ X0) (σ X1)
       grind)
    | exact superpose eq430110 eq624704
    | (have j0 := eq624704 X0 X1 X2
       grind)
    | exact resolve eq624704 eq430110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430110 eq624704
  have eq624706 : ∀ X0 X1 : G, y = (M.op y (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op (σ X0) y)))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq624705 X0 X1 x
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq624705
    | (have j0 := eq624705 X0 X1 x
       grind)
    | exact resolve eq624705 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624705
  have eq624707 : ∀ X0 X1 : G, y = (M.op y (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op (σ X0) y)))) ∨ (σ X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq624706 X0 X1
       have i₂ := eq152973 (σ X1)
       grind)
    | exact superpose eq152973 eq624706
    | (have j0 := eq624706 X0 X1
       grind)
    | exact resolve eq624706 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624706
  have eq1398452 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k y X1) ∨ y = (k y X1) ∨ y = X1 ∨ (k X2 (k y X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq248640 X1 (k y X1)
       have i₂ := eq147130 (k y X1) X0 X2
       grind)
    | exact superpose eq147130 eq248640
    | (have j0 := eq248640 (k y X1) (k y X1)
       have j1 := eq147130 X1 X1 y
       grind)
    | exact resolve eq248640 eq147130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147130 eq248640
  have eq1399225 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k y X1) ∨ y = (k y X1) ∨ (k X2 (k y X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1398452 X0 X1 X2
       have j1 := eq165127 X1 y
       grind)
    | (have r₁ := eq1398452 X0 X1 X2
       have r₂ := eq165127 (k y X1) X1
       grind)
    | (have r₁ := eq1398452 X0 X0 X2
       have r₂ := eq165127 X0 X1
       grind)
    | (have r₁ := eq1398452 X0 y X2
       have r₂ := eq165127 y X1
       grind)
    | exact resolve eq1398452 eq165127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1398452
  have eq1399430 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (k y X1) ∨ (k X2 (k y X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1399225 X0 X1 X2
       have j1 := eq165127 (k y X1) X2
       grind)
    | (have r₁ := eq1399225 X0 X1 X2
       have r₂ := eq165127 (k y X1) X1
       grind)
    | (have r₁ := eq1399225 X0 X1 y
       have r₂ := eq165127 (k y (k y X1)) X1
       grind)
    | exact resolve eq1399225 eq165127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165127 eq1399225
  have eq1399592 : ∀ X1 X2 : G, (k X2 (k y X1)) = X2 ∨ (M.op y X1) = (k y X1) := by
    intro X1 X2
    first
    | (have i₁ := eq1399430 x X1 X2
       have i₂ := eq152973 x
       grind)
    | exact superpose eq152973 eq1399430
    | (have j0 := eq1399430 x X1 X2
       grind)
    | exact resolve eq1399430 eq152973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152973 eq1399430
  have eq1400235 : ∀ X0 : G, y = (τ (τ (k y X0))) ∨ y = (τ (τ (k y X0))) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq155745 (k y X0)
       have i₂ := eq1399592 X0 (k y X0)
       grind)
    | exact superpose eq1399592 eq155745
    | (have j0 := eq155745 (k y X0)
       have j1 := eq1399592 X0 x
       grind)
    | exact resolve eq155745 eq1399592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155745 eq1399592
  have eq1400862 : ∀ X0 : G, y = (τ (τ (k y X0))) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq1400235 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400235
  have eq1401220 : ∀ X0 : G, y = (τ (k y (τ X0))) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq1400862 X0
       have i₂ := eq154368 X0
       grind)
    | exact superpose eq154368 eq1400862
    | (have j0 := eq1400862 X0
       grind)
    | exact resolve eq1400862 eq154368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1400862
  have eq1401521 : ∀ X0 : G, y = (k y (τ (τ X0))) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq1401220 X0
       have i₂ := eq154368 (τ X0)
       grind)
    | exact superpose eq154368 eq1401220
    | (have j0 := eq1401220 X0
       grind)
    | exact resolve eq1401220 eq154368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154368 eq1401220
  have eq1409664 : ∀ X0 : G, y = (M.op y (M.op (σ (τ (τ X0))) (M.op (σ y) (M.op (σ y) y)))) ∨ y = (σ (τ (τ X0))) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq624707 y (τ (τ X0))
       have i₂ := eq1401521 X0
       grind)
    | exact superpose eq1401521 eq624707
    | (have j0 := eq624707 X0 (τ (τ X0))
       have j1 := eq1401521 X0
       grind)
    | exact resolve eq624707 eq1401521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624707 eq1401521
  have eq1409718 : ∀ X0 : G, y = (M.op y (M.op (σ (τ (τ X0))) (M.op y (M.op y y)))) ∨ y = (σ (τ (τ X0))) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq1409664 X0
       have i₂ := eq153960
       grind)
    | exact superpose eq153960 eq1409664
    | (have j0 := eq1409664 X0
       grind)
    | exact resolve eq1409664 eq153960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153960 eq1409664
  have eq1409954 : ∀ X0 : G, y = (σ (τ (τ X0))) ∨ y = (σ (τ (τ X0))) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq1409718 X0
       have i₂ := eq40 y y (σ (τ (τ X0)))
       grind)
    | exact superpose eq40 eq1409718
    | (have j0 := eq1409718 X0
       grind)
    | exact resolve eq1409718 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1409718
  have eq1409955 : ∀ X0 : G, y = (σ (τ (τ X0))) ∨ (k y X0) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq1409954 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409954
  have eq1410003 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ (τ X0) = y := by
    intro X0
    first
    | (have i₁ := eq1409955 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq1409955
    | (have j0 := eq1409955 X0
       grind)
    | exact resolve eq1409955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1409955
  have eq1410329 : ∀ X0 : G, (σ X0) = (M.op y (σ (M.op X0 y))) ∨ y = (M.op X0 y) ∨ y = (τ (σ (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq301732 X0
       have i₂ := eq1410003 (σ (M.op X0 y))
       grind)
    | exact superpose eq1410003 eq301732
    | (have j0 := eq301732 X0
       have j1 := eq1410003 (σ (M.op X0 y))
       grind)
    | exact resolve eq301732 eq1410003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301732 eq1410003
  have eq1411117 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ X0) = (M.op y (σ (M.op X0 y))) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq1410329 X0
       have i₂ := eq10 (M.op X0 y)
       grind)
    | exact superpose eq10 eq1410329
    | (have j0 := eq1410329 X0
       grind)
    | exact resolve eq1410329 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410329
  have eq1411118 : ∀ X0 : G, (σ X0) = (M.op y (σ (M.op X0 y))) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq1411117 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411117
  have eq1429351 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq157652 (σ (M.op X0 y))
       have i₂ := eq1411118 X0
       grind)
    | exact superpose eq1411118 eq157652
    | (have j1 := eq1411118 X0
       grind)
    | exact resolve eq157652 eq1411118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157652 eq1411118
  have eq1437868 : (M.op (σ x) y) ≠ (M.op (σ x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq155128
       have i₂ := eq1429351 x
       grind)
    | exact superpose eq1429351 eq155128
    | (have j1 := eq1429351 x
       grind)
    | (have r₁ := eq155128
       have r₂ := eq1429351 x
       grind)
    | exact resolve eq155128 eq1429351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155128 eq1429351
  have eq1438059 : y = (M.op x y) := by grind
  clear eq1437868
  have eq1438478 : x = (M.op y (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq165905 y x
       have i₂ := eq1438059
       grind)
    | exact superpose eq1438059 eq165905
    | exact resolve eq165905 eq1438059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165905 eq1438059
  have eq1438536 : x = y := by
    first
    | (have i₁ := eq1438478
       have i₂ := eq161257 y y
       grind)
    | (have i₁ := eq1438478
       have i₂ := eq161257 x (M.op y (M.op y (M.op y y)))
       grind)
    | exact superpose eq161257 eq1438478
    | exact resolve eq1438478 eq161257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161257 eq1438478
  have eq1438828 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1438536
       grind)
    | exact superpose eq1438536 eq16
    | exact resolve eq16 eq1438536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438536
  have eq1439840 : False := by grind
  exact eq1439840

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pxy_pyy_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
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
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq35 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq43 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq35 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq47 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq43 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq43 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq47 X1 X0
       grind)
    | (have r₁ := eq55 X1 X0
       have r₂ := eq47 X0 X1
       grind)
    | exact resolve eq55 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq55
  have eq67 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq64
    | (have j0 := eq64 X0 X1
       grind)
    | exact resolve eq64 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq64
  have eq145 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq149 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq145 X0 X1
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq145 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | (have r₁ := eq145 X1 X1
       have r₂ := eq67 X1 X1
       grind)
    | exact resolve eq145 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq145
  have eq680 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq149 (σ X0) (σ X1)
       grind)
    | exact superpose eq149 eq15
    | exact resolve eq15 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq683 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq680 X0 X1
       have i₂ := eq149 X0 X1
       grind)
    | exact superpose eq149 eq680
    | exact resolve eq680 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149 eq680
  have eq686 : False := by grind
  exact eq686

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pxy_pyx_Equation2146 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
       have i₂ := eq9 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq49 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq45 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X0 ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq42 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq42 X1 X1 X2
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq47 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq48 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq48 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq49 X0 X1
       grind)
    | (have r₁ := eq57 X0 X1
       have r₂ := eq49 X0 X1
       grind)
    | exact resolve eq57 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq65
    | (have j0 := eq65 X0 X1
       grind)
    | exact resolve eq65 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq26 (σ X0)
       grind)
    | exact superpose eq26 eq15
    | exact resolve eq15 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq72
    | exact resolve eq72 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq72
  have eq78 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15
    | exact resolve eq15 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq101 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20 X0 X2 (M.op (M.op X1 X1) (M.op X2 X2))
       have i₂ := eq9 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq9 eq20
    | exact resolve eq20 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq20 (M.op X0 X0) X0 X1
       grind)
    | exact superpose eq20 eq20
    | exact resolve eq20 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op X0 (M.op X1 (M.op X2 X2))) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 (M.op X2 (M.op X0 (M.op X1 X1)))
       have i₂ := eq20 X0 X1 X2
       grind)
    | exact superpose eq20 eq49
    | (have r₁ := eq49 X2 (M.op X2 (M.op X2 (M.op X1 X1)))
       have r₂ := eq20 X2 X1 X2
       grind)
    | exact resolve eq49 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq126 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq53 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq208 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X3 (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) X1)))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X3 (M.op X2 X2) X4
       have i₂ := eq21 X1 X0 (M.op X2 X2) X2
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) (M.op X4 (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) X1))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op X3 X3) X2 X4
       have i₂ := eq21 X1 X0 (M.op X2 X2) X3
       grind)
    | (have i₁ := eq20 (M.op (M.op X1 X1) (M.op (M.op X1 X1) X2)) X1 X2
       have i₂ := eq21 (M.op X1 X1) X1 X2 X3
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 (M.op (M.op X3 X3) (M.op X4 X4))))) X1) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 (M.op X3 X3) X4 X2
       have i₂ := eq21 X1 X0 (M.op X2 (M.op (M.op X3 X3) (M.op X4 X4))) X3
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X0 X0) X1)) = (M.op (M.op X3 X3) (M.op (M.op X2 (M.op X4 X4)) X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq20 X2 X4 (M.op (M.op X3 X3) (M.op (M.op X2 (M.op X4 X4)) X1))
       have i₂ := eq21 (M.op X2 (M.op X4 X4)) X3 X1 X0
       grind)
    | (have i₁ := eq20 X0 X1 (M.op X3 X3)
       have i₂ := eq21 X0 X1 (M.op X0 (M.op X1 X1)) X3
       grind)
    | exact superpose eq21 eq20
    | exact resolve eq20 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = X0 ∨ (M.op X0 (M.op (M.op X0 X0) X2)) = (k (M.op (M.op X0 X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (M.op X0 X0) x X2 X1
       have i₂ := eq52 X0 x (M.op (M.op X0 X0) X2)
       grind)
    | exact superpose eq52 eq21
    | (have j1 := eq52 X0 X1 (M.op (M.op X0 X0) X2)
       grind)
    | exact resolve eq21 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq379 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq70 X1 X2
       have i₂ := eq102 X0 X1
       grind)
    | (have i₁ := eq70 X1 X2
       have i₂ := eq102 X1 X0
       grind)
    | exact superpose eq102 eq70
    | (have j0 := eq70 X1 X2
       grind)
    | exact resolve eq70 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq380 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 X2
       have i₂ := eq102 X0 X2
       grind)
    | (have i₁ := eq9 X2 X1 X2
       have i₂ := eq102 X2 X0
       grind)
    | exact superpose eq102 eq9
    | exact resolve eq9 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1157 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (M.op (M.op X2 X2) X1) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq52 X0 X2 X1
       grind)
    | exact superpose eq52 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq52 X0 X2 X1
       grind)
    | exact resolve eq33 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq52
  have eq1287 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (M.op (M.op X2 X2) X1) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1157 X0 X1 X2
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq1157
    | (have j0 := eq1157 X0 X1 X2
       grind)
    | exact resolve eq1157 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1332 : ∀ X0 X1 X2 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (M.op (M.op X2 X2) X1) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1287 X0 X1 X2
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq1287
    | (have j0 := eq1287 X0 X1 X2
       grind)
    | exact resolve eq1287 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287
  have eq1350 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1332 X0 X1 x
       have i₂ := eq380 X0 x X1
       grind)
    | exact superpose eq380 eq1332
    | (have j0 := eq1332 X0 X1 x
       grind)
    | exact resolve eq1332 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq1332
  have eq1518 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 (σ X0) X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq102
    | exact resolve eq102 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1699 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X0 X0) (M.op X1 X1)))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq20 (M.op X2 X2) X2 X3
       have i₂ := eq101 (M.op X2 X2) X0 X1
       grind)
    | (have i₁ := eq20 (M.op X1 X1) X2 X2
       have i₂ := eq101 X0 X1 X2
       grind)
    | exact superpose eq101 eq20
    | exact resolve eq20 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq101
  have eq2053 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq116 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq2197 : ∀ X0 X1 X2 X3 : G, (k (σ X2) (k (k X0 (σ X1)) (σ X3))) = (σ (k X2 (k (k (τ X0) X1) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq78 (k X0 (σ X1)) X3 X2
       have i₂ := eq80 X0 X1
       grind)
    | exact superpose eq80 eq78
    | exact resolve eq78 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq13093 : ∀ X0 X1 X2 X3 X4 X6 : G, (M.op (M.op X0 (M.op (M.op X1 X1) (M.op X2 (M.op (M.op X3 X3) (M.op X4 X4))))) (M.op X0 (M.op X6 X6))) = X2 := by
    intro X0 X1 X2 X3 X4 X6
    first
    | (have i₁ := eq217 x (M.op X0 (M.op X6 X6)) X2 X3 X4
       have i₂ := eq222 X1 (M.op X2 (M.op (M.op X3 X3) (M.op X4 X4))) X0 x X6
       grind)
    | (have i₁ := eq217 X0 (M.op X0 X0) X2 X3 X4
       have i₂ := eq222 X0 (M.op X2 (M.op (M.op X3 X3) (M.op X4 X4))) (M.op X0 X0) X3 X4
       grind)
    | exact superpose eq222 eq217
    | exact resolve eq217 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq222
  have eq13377 : ∀ X0 X2 X6 : G, (M.op (M.op X0 X2) (M.op X0 (M.op X6 X6))) = X2 := by
    intro X0 X2 X6
    first
    | (have i₁ := eq13093 X0 x X2 x x X6
       have i₂ := eq1699 x x x X2
       grind)
    | exact superpose eq1699 eq13093
    | exact resolve eq13093 eq1699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1699 eq13093
  have eq26001 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 X0) = (M.op X2 X2) ∨ (M.op X0 (M.op (M.op X0 X0) (M.op X1 (M.op (M.op (M.op X3 X3) (M.op X4 (M.op X5 X5))) X4)))) = (k (M.op (M.op X0 X0) (M.op X1 (M.op (M.op (M.op X3 X3) (M.op X4 (M.op X5 X5))) X4))) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq208 X3 X4 X5 X1 (M.op X2 X2)
       have i₂ := eq293 X0 X2 (M.op X1 (M.op (M.op (M.op X3 X3) (M.op X4 (M.op X5 X5))) X4))
       grind)
    | (have i₁ := eq208 X0 X1 X2 X3 X4
       have i₂ := eq293 (M.op X4 (M.op X3 (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) X1))) X1 X2
       grind)
    | exact superpose eq293 eq208
    | (have j1 := eq293 X0 X1 (M.op X1 (M.op (M.op (M.op X3 X3) (M.op X4 (M.op X5 X5))) X4))
       grind)
    | exact resolve eq208 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq293
  have eq26042 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26001 x x X2 X0 X1 X2
       have i₂ := eq215 X0 X1 X2 x x
       grind)
    | exact superpose eq215 eq26001
    | (have j0 := eq26001 X0 X1 X2 x x x
       grind)
    | exact resolve eq26001 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq26001
  have eq102696 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1350 x y
       grind)
    | exact superpose eq1350 eq16
    | (have j1 := eq1350 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1350 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1350 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq1350 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq1350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1350
  have eq102982 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by grind
  clear eq102696
  have eq280389 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) (M.op X2 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X1 X1)
       have i₂ := eq1518 X0 (M.op X1 X1)
       grind)
    | exact superpose eq1518 eq9
    | exact resolve eq9 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293883 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (M.op (σ X0) (M.op X1 X1)))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (M.op (σ X0) (M.op (σ X0) (M.op X1 X1))) X0
       have i₂ := eq2053 (σ X0) X1
       grind)
    | exact superpose eq2053 eq80
    | exact resolve eq80 eq2053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq293908 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) (M.op (σ X0) (M.op X1 X1)))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq293883 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq293883
    | exact resolve eq293883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293883
  have eq298672 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (M.op X0 X0))) ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13377 (σ x) (σ y) X0
       have i₂ := eq102982
       grind)
    | exact superpose eq102982 eq13377
    | exact resolve eq13377 eq102982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13377 eq102982
  have eq300299 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq298672 x
       have i₂ := eq280389 x x (σ x)
       grind)
    | exact superpose eq280389 eq298672
    | exact resolve eq298672 eq280389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280389 eq298672
  have eq303942 : (M.op x x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq300299
       grind)
    | exact superpose eq300299 eq10
    | exact resolve eq10 eq300299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300299
  have eq304119 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq303942
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq303942
    | exact resolve eq303942 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303942
  have eq310585 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq126 X2 X1
       have i₂ := eq26042 X1 X2 X0
       grind)
    | (have i₁ := eq126 X2 X2
       have i₂ := eq26042 X0 X1 X2
       grind)
    | exact superpose eq26042 eq126
    | (have j0 := eq126 X2 X1
       have j1 := eq26042 X1 X2 X2
       grind)
    | (have r₁ := eq126 X2 X2
       have r₂ := eq26042 X2 X2 X2
       grind)
    | (have r₁ := eq126 X0 X0
       have r₂ := eq26042 X0 X0 X0
       grind)
    | exact resolve eq126 eq26042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq26042
  have eq312390 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq310585 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310585
  have eq312668 : ∀ X1 X2 : G, (M.op X1 X2) = (k X2 X1) := by
    intro X1 X2
    first
    | (have j0 := eq312390 x X1 X2
       have j1 := eq379 x X1 X2
       grind)
    | (have r₁ := eq312390 x X1 X2
       have r₂ := eq379 x X1 X2
       grind)
    | (have r₁ := eq312390 X2 x x
       have r₂ := eq379 x X2 X2
       grind)
    | exact resolve eq312390 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379 eq312390
  have eq322283 : ∀ X0 : G, x = (M.op X0 X0) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq102 x X0
       have i₂ := eq304119
       grind)
    | exact superpose eq304119 eq102
    | exact resolve eq102 eq304119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq304119
  have eq353341 : ∀ X0 : G, y = (τ (σ x)) ∨ x = (M.op X0 X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq10 y
       have i₂ := eq322283 X0
       grind)
    | exact superpose eq322283 eq10
    | (have j1 := eq322283 X0
       grind)
    | exact resolve eq10 eq322283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322283
  have eq353501 : ∀ X0 : G, x = y ∨ x = (M.op X0 X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq353341 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq353341
    | (have j0 := eq353341 X0
       grind)
    | exact resolve eq353341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353341
  have eq353502 : ∀ X0 : G, x = y ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq353501 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353501
  have eq377256 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq353502 X0
       grind)
    | exact superpose eq353502 eq16
    | (have j1 := eq353502 X0
       grind)
    | exact resolve eq16 eq353502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353502
  have eq378277 : ∀ X0 : G, x = (M.op X0 X0) := by
    intro X0
    first
    | (have j0 := eq377256 X0
       grind)
    | (have r₁ := eq377256 X0
       have r₂ := eq1518 x (σ x)
       grind)
    | exact resolve eq377256 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518 eq377256
  have eq415596 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ y)) ≠ (σ (M.op (M.op X0 X0) y)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq378277 X0
       grind)
    | exact superpose eq378277 eq16
    | exact resolve eq16 eq378277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378277
  have eq467911 : ∀ X0 X1 X2 X3 : G, (σ (k X1 (k (k (τ (M.op (σ X0) (M.op (σ X0) (M.op X2 X2)))) X0) X3))) = (k (σ X1) (k (σ X0) (σ X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2197 (M.op (σ X0) (M.op (σ X0) (M.op X2 X2))) X0 X1 X3
       have i₂ := eq2053 (σ X0) X2
       grind)
    | exact superpose eq2053 eq2197
    | exact resolve eq2197 eq2053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053 eq2197
  have eq468092 : ∀ X0 X1 X2 X3 : G, (σ (k X1 (k (k (τ (M.op (σ X0) (M.op (σ X0) (M.op X2 X2)))) X0) X3))) = (M.op (k (σ X0) (σ X3)) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq467911 X0 X1 X2 X3
       have i₂ := eq312668 (k (σ X0) (σ X3)) (σ X1)
       grind)
    | exact superpose eq312668 eq467911
    | exact resolve eq467911 eq312668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467911
  have eq468295 : ∀ X0 X1 X2 X3 : G, (σ (k X1 (k (k (τ (M.op (σ X0) (M.op (σ X0) (M.op X2 X2)))) X0) X3))) = (M.op (σ (k X0 X3)) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq468092 X0 X1 X2 X3
       have i₂ := eq15 X0 X3
       grind)
    | exact superpose eq15 eq468092
    | exact resolve eq468092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468092
  have eq468497 : ∀ X0 X1 X2 X3 : G, (σ (k X1 (k (k (τ (M.op (σ X0) (M.op (σ X0) (M.op X2 X2)))) X0) X3))) = (M.op (σ (M.op X3 X0)) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq468295 X0 X1 X2 X3
       have i₂ := eq312668 X3 X0
       grind)
    | exact superpose eq312668 eq468295
    | exact resolve eq468295 eq312668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468295
  have eq468699 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X3 X0)) (σ X1)) = (σ (M.op (k (k (τ (M.op (σ X0) (M.op (σ X0) (M.op X2 X2)))) X0) X3) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq468497 X0 X1 X2 X3
       have i₂ := eq312668 (k (k (τ (M.op (σ X0) (M.op (σ X0) (M.op X2 X2)))) X0) X3) X1
       grind)
    | exact superpose eq312668 eq468497
    | exact resolve eq468497 eq312668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468497
  have eq468899 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X3 X0)) (σ X1)) = (σ (M.op (M.op X3 (k (τ (M.op (σ X0) (M.op (σ X0) (M.op X2 X2)))) X0)) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq468699 X0 X1 X2 X3
       have i₂ := eq312668 X3 (k (τ (M.op (σ X0) (M.op (σ X0) (M.op X2 X2)))) X0)
       grind)
    | exact superpose eq312668 eq468699
    | exact resolve eq468699 eq312668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312668 eq468699
  have eq469088 : ∀ X0 X1 X3 : G, (M.op (σ (M.op X3 X0)) (σ X1)) = (σ (M.op (M.op X3 X0) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq468899 X0 X1 x X3
       have i₂ := eq293908 X0 x
       grind)
    | exact superpose eq293908 eq468899
    | exact resolve eq468899 eq293908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293908 eq468899
  have eq469261 : False := by grind
  exact eq469261
