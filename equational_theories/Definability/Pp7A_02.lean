import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pxx_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  clear eq24
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq14 X0 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq75 y x
       grind)
    | exact superpose eq75 eq72
    | (have j1 := eq75 y x
       grind)
    | exact resolve eq72 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq205 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq212 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq109 eq75
    | (have j0 := eq75 (σ y) (σ x)
       grind)
    | exact resolve eq75 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq705
    | exact resolve eq705 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705
  have eq709 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq706
       have r₂ := eq27
       grind)
    | exact resolve eq706 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq713 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq709 eq53
    | exact resolve eq53 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq718 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq713
    | (have j0 := eq713 X0
       grind)
    | exact resolve eq713 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq756 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq718 eq212
    | exact resolve eq212 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq718
  have eq762 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x y))) = X0 ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 y X0 x
       have i₂ := eq756 X1
       grind)
    | exact superpose eq756 eq53
    | (have j1 := eq756 X1
       grind)
    | exact resolve eq53 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq767 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x y))) = X0 ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq762
    | (have j0 := eq762 X0 X1
       grind)
    | exact resolve eq762 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq864 : ∀ X0 X1 : G, (M.op X1 (σ x)) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0
       have i₂ := eq767 X0 (M.op x (M.op y sF0))
       grind)
    | exact superpose eq767 eq205
    | (have j1 := eq767 X0 X1
       grind)
    | exact resolve eq205 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq868 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq864 (M.op X1 X1) X1
       grind)
    | exact superpose eq864 eq13
    | (have j0 := eq13 X0 (σ x)
       have j1 := eq864 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq864 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq864 x X1
       grind)
    | exact resolve eq13 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq882 : ∀ X0 X1 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op X1 x) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq868 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq909 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq109
       have i₂ := eq882 X0 (k sF3 sF2)
       grind)
    | exact superpose eq882 eq109
    | (have j1 := eq882 X0 y
       grind)
    | exact resolve eq109 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq882
  have eq915 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq909
    | (have j0 := eq909 y
       grind)
    | exact resolve eq909 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq917 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq915 y
       grind)
    | (have r₁ := eq915 X0
       have r₂ := eq27
       grind)
    | exact resolve eq915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq924 : y ≠ y ∨ y = (M.op y x) := by
    first
    | (have j0 := eq917 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq925 : y = (M.op y x) := by grind
  clear eq924
  have eq986 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 y X0 x
       have i₂ := eq925
       grind)
    | exact superpose eq925 eq53
    | exact resolve eq53 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq925
  have eq991 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq986 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq986
    | (have j0 := eq986 X0
       grind)
    | exact resolve eq986 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1038 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq991 eq205
    | exact resolve eq205 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq991
  have eq1128 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1038 x
       grind)
    | exact superpose eq1038 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1038 x
       grind)
    | exact resolve eq13 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1147 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1128 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1155 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1147 x
       grind)
    | exact superpose eq1147 eq43
    | exact resolve eq43 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1156 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1147 y
       grind)
    | exact superpose eq1147 eq72
    | exact resolve eq72 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1147
  have eq1161 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1156
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1156
    | exact resolve eq1156 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1156
  have eq1162 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1155
       have i₂ := eq1038 x
       grind)
    | exact superpose eq1038 eq1155
    | exact resolve eq1155 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq1155
  have eq1163 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq1161
    | exact resolve eq1161 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1161
  have eq1164 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1162
    | exact resolve eq1162 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1162
  have eq1181 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1164 eq75
    | (have j0 := eq75 (σ x) (σ x)
       grind)
    | exact resolve eq75 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1164
  have eq1182 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1181
  have eq1268 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq1182 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1182
       grind)
    | exact resolve eq13 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1274 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq1268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1274 eq1163
    | exact resolve eq1163 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163 eq1274
  have eq1504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1497
    | exact resolve eq1497 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1497
  have eq1512 : False := by grind
  exact eq1512

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyx_pxy_pyx_Equation1061 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1061 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  clear eq24
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq14 X0 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq75 y x
       grind)
    | exact superpose eq75 eq72
    | (have j1 := eq75 y x
       grind)
    | exact resolve eq72 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
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
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq205 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq212 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) = X0 := by
    intro X0
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq583 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq109 eq75
    | (have j0 := eq75 (σ y) (σ x)
       grind)
    | exact resolve eq75 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq583
    | exact resolve eq583 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq587 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq584
       have r₂ := eq27
       grind)
    | exact resolve eq584 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq589 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq587 eq53
    | exact resolve eq53 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq594 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq589
    | (have j0 := eq589 X0
       grind)
    | exact resolve eq589 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq683 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq594 eq212
    | exact resolve eq212 eq594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq594
  have eq762 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x y))) = X0 ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 y X0 x
       have i₂ := eq683 X1
       grind)
    | exact superpose eq683 eq53
    | (have j1 := eq683 X1
       grind)
    | exact resolve eq53 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683
  have eq767 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op x y))) = X0 ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq762
    | (have j0 := eq762 X0 X1
       grind)
    | exact resolve eq762 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq864 : ∀ X0 X1 : G, (M.op X1 (σ x)) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0
       have i₂ := eq767 X0 (M.op x (M.op y sF0))
       grind)
    | exact superpose eq767 eq205
    | (have j1 := eq767 X0 X1
       grind)
    | exact resolve eq205 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767
  have eq868 : ∀ X0 X1 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op X1 x) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq864 (M.op X1 X1) X1
       grind)
    | exact superpose eq864 eq13
    | (have j0 := eq13 X0 (σ x)
       have j1 := eq864 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq864 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq864 x X1
       grind)
    | exact resolve eq13 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq882 : ∀ X0 X1 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (M.op X1 x) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq868 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq909 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq109
       have i₂ := eq882 X0 (k sF3 sF2)
       grind)
    | exact superpose eq882 eq109
    | (have j1 := eq882 X0 y
       grind)
    | exact resolve eq109 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq882
  have eq915 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq909
    | (have j0 := eq909 y
       grind)
    | exact resolve eq909 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq917 : ∀ X0 : G, y = (M.op y x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq915 y
       grind)
    | (have r₁ := eq915 X0
       have r₂ := eq27
       grind)
    | exact resolve eq915 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq924 : y ≠ y ∨ y = (M.op y x) := by
    first
    | (have j0 := eq917 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq925 : y = (M.op y x) := by grind
  clear eq924
  have eq986 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq53 y X0 x
       have i₂ := eq925
       grind)
    | exact superpose eq925 eq53
    | exact resolve eq53 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq925
  have eq991 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq986 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq986
    | (have j0 := eq986 X0
       grind)
    | exact resolve eq986 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq1038 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq991 eq205
    | exact resolve eq205 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq991
  have eq1128 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1038 x
       grind)
    | exact superpose eq1038 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1038 x
       grind)
    | exact resolve eq13 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1147 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1128 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128
  have eq1155 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1147 x
       grind)
    | exact superpose eq1147 eq43
    | exact resolve eq43 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1156 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1147 y
       grind)
    | exact superpose eq1147 eq72
    | exact resolve eq72 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1147
  have eq1161 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1156
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1156
    | exact resolve eq1156 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1156
  have eq1162 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1155
       have i₂ := eq1038 x
       grind)
    | exact superpose eq1038 eq1155
    | exact resolve eq1155 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq1155
  have eq1163 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq20 eq1161
    | exact resolve eq1161 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1161
  have eq1164 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1162
    | exact resolve eq1162 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1162
  have eq1181 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1164 eq75
    | (have j0 := eq75 (σ x) (σ x)
       grind)
    | exact resolve eq75 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1164
  have eq1182 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1181
  have eq1268 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq1182 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1182
       grind)
    | exact resolve eq13 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1274 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq1268 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1497 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1274 eq1163
    | exact resolve eq1163 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163 eq1274
  have eq1504 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1497
    | exact resolve eq1497 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1497
  have eq1512 : False := by grind
  exact eq1512

/-- `Equation1061`: `x = x ◇ ((y ◇ (z ◇ y)) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pxy_Equation1061 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1061 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1061.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X1)) X2)) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op X0 (M.op (M.op y (M.op x y)) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X2 (M.op X0 X2)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X0 (M.op X2 (M.op X0 X2))
       have i₂ := eq14 X0 X2 X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 (M.op y y) y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq78
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq78
    | exact resolve eq78 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq95 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq91
  have eq96 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq95
  have eq127 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq96
       grind)
    | exact superpose eq96 eq16
    | exact resolve eq16 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq209 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq377 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) (σ (M.op X0 X0))) (σ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3227 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq377 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq56 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
       grind)
    | exact superpose eq56 eq377
    | exact resolve eq377 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq3411 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1))))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3227 X0 X1 X2
       have i₂ := eq45 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq45 eq3227
    | exact resolve eq3227 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq3433 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3411 X0 X1 X2
       have i₂ := eq56 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
       grind)
    | exact superpose eq56 eq3411
    | exact resolve eq3411 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3411
  have eq3450 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3433 X0 X1 X2
       have i₂ := eq45 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq45 eq3433
    | exact resolve eq3433 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq3433
  have eq3467 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3450 X0 X1 X2
       have i₂ := eq56 X0 (M.op X0 (M.op X1 (M.op X0 X1))) X1
       grind)
    | exact superpose eq56 eq3450
    | exact resolve eq3450 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq3450
  have eq15415 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (M.op (σ y) (σ y)) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq15416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq15415
    | exact resolve eq15415 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15415
  have eq15427 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq15416
       have r₂ := eq28
       grind)
    | exact resolve eq15416 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15416
  have eq16116 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq15427 eq127
    | exact resolve eq127 eq15427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq15427
  have eq16155 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq30 eq16116
    | exact resolve eq16116 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16116
  have eq16156 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16155
  have eq16172 : ∀ X0 : G, (M.op X0 (M.op (M.op y y) y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14 X0 y y
       have i₂ := eq16156
       grind)
    | exact superpose eq16156 eq14
    | exact resolve eq14 eq16156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17202 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16172 X0
       have i₂ := eq16156
       grind)
    | exact superpose eq16156 eq16172
    | exact resolve eq16172 eq16156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16172
  have eq17315 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq17202 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17202
  have eq17339 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq17315 X0
       have i₂ := eq16156
       grind)
    | exact superpose eq16156 eq17315
    | exact resolve eq17315 eq16156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16156 eq17315
  have eq17452 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq17339 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17339
  have eq17481 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq17452 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq17452
    | (have j0 := eq17452 x
       grind)
    | exact resolve eq17452 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17452
  have eq17630 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17481 eq30
    | exact resolve eq30 eq17481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17481
  have eq17747 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq17630
    | exact resolve eq17630 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq17630
  have eq17748 : x = (M.op x y) ∨ x = y := by grind
  clear eq17747
  have eq17765 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq17748 eq21
    | exact resolve eq21 eq17748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17811 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq17748 eq209
    | exact resolve eq209 eq17748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq17748
  have eq17886 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq17765
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq17765
    | exact resolve eq17765 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17765
  have eq17901 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq17886 eq27
    | exact resolve eq27 eq17886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17886
  have eq21667 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3467 y x X0
       have i₂ := eq17811 y
       grind)
    | exact superpose eq17811 eq3467
    | exact resolve eq3467 eq17811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467 eq17811
  have eq21818 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq21667 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21667
    | (have j0 := eq21667 X0
       grind)
    | exact resolve eq21667 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21667
  have eq22087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq21818 eq17901
    | exact resolve eq17901 eq21818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17901 eq21818
  have eq22096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq22087
  have eq22108 : x = y := by
    first
    | (have r₁ := eq22096
       have r₂ := eq28
       grind)
    | exact resolve eq22096 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22096
  have eq22140 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq22108
       grind)
    | exact superpose eq22108 eq19
    | exact resolve eq19 eq22108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq22141 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq22108
       grind)
    | exact superpose eq22108 eq25
    | exact resolve eq25 eq22108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq22108
  have eq22260 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22141
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22141
    | exact resolve eq22141 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq22141
  have eq22275 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22260 eq27
    | exact resolve eq27 eq22260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22260
  have eq22498 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq22275 eq69
    | exact resolve eq69 eq22275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq22275
  have eq22536 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq22498
       have i₂ := eq22140
       grind)
    | exact superpose eq22140 eq22498
    | exact resolve eq22498 eq22140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22140 eq22498
  have eq22545 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22536 eq15
    | exact resolve eq15 eq22536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22536
  have eq22590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq22545
    | exact resolve eq22545 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22545
  have eq22599 : False := by grind
  exact eq22599

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pxy_pxy_pxx_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
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
  have eq29 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq54 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq54 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq55 (σ X0)
       grind)
    | exact superpose eq55 eq15
    | exact resolve eq15 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq55 (τ X0)
       grind)
    | exact superpose eq55 eq18
    | exact resolve eq18 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq57 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq57
    | exact resolve eq57 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq55 X0
       grind)
    | exact superpose eq55 eq63
    | exact resolve eq63 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq63
  have eq75 : ∀ X0 X1 : G, (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq66
    | exact resolve eq66 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq66 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq66
    | exact resolve eq66 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq86 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 X1
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq90
    | (have j0 := eq90 X0 X1
       grind)
    | exact resolve eq90 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq90
  have eq103 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq10
    | exact resolve eq10 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 (k (τ X0) X1) X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq93
    | exact resolve eq93 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | (have j0 := eq93 X1 X1
       grind)
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq147 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq133 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq133
    | (have j0 := eq133 X0 X1
       grind)
    | exact resolve eq133 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq149 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131 X0 X1 X2
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq131
    | (have j0 := eq131 X0 X1 X2
       grind)
    | exact resolve eq131 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq150 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ (M.op (k (τ X0) X1) (k (τ X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq130 X0 X1 X2
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq130
    | (have j0 := eq130 X0 X1 X2
       grind)
    | exact resolve eq130 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq153 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq147 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq147 X0 X0
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq147 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq147
  have eq155 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq149 X0 X1 X2
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq149
    | (have j0 := eq149 X0 X1 X2
       grind)
    | exact resolve eq149 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq149
  have eq156 : ∀ X0 X1 X2 : G, (M.op (k X0 (σ X1)) (k X0 (σ X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq150 X0 X1 X2
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq150
    | (have j0 := eq150 X0 X1 X2
       grind)
    | exact resolve eq150 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq150
  have eq169 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 (τ (M.op X0 X0))) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (τ X0)
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq9
    | exact resolve eq9 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq501 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq153 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq153
    | exact resolve eq153 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq524 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq501 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq501
    | (have j0 := eq501 X0 X1
       grind)
    | exact resolve eq501 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq501
  have eq535 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq524 X0 (τ X1)
       grind)
    | exact superpose eq524 eq18
    | (have j1 := eq524 X0 (τ X1)
       grind)
    | exact resolve eq18 eq524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq524
  have eq972 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X2)) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 X0 (M.op (M.op X1 (M.op X2 X2)) (τ X0))
       have i₂ := eq9 (τ X0) X1 X2
       grind)
    | exact superpose eq9 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1020 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X2)) (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq972 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1055 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X2)) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1020 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1020
    | (have j0 := eq1020 X0 X1 X2
       grind)
    | exact resolve eq1020 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1094 : ∀ X0 X1 X2 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (k X0 (σ (M.op (M.op X1 (M.op X2 X2)) (τ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1055 X0 X1 X2
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq1055
    | (have j0 := eq1055 X0 X1 X2
       grind)
    | exact resolve eq1055 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq1055
  have eq1487 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k (k (σ X0) X1) X3) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq155 X0 X1 X2
       grind)
    | exact superpose eq155 eq13
    | (have j0 := eq13 (k (σ X0) X1) X1
       have j1 := eq155 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq155 X0 X1 X2
       grind)
    | exact resolve eq13 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1515 : ∀ X0 X1 X2 : G, (k (σ X0) X1) ≠ (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq155 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq1522 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k (k (σ X0) X1) X3) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq1487 X0 X1 X2 X3
       have j1 := eq1515 X0 X1 X2
       grind)
    | (have r₁ := eq1487 X0 X1 X2 X3
       have r₂ := eq1515 X0 X1 X2
       grind)
    | exact resolve eq1487 eq1515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487 eq1515
  have eq1734 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (k X0 (σ X1)) (k X0 (σ X1))) ∨ (σ (k (k (τ X0) X1) X2)) = (M.op (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq156 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq2210 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq535
    | exact resolve eq535 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq2260 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2210 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2210
    | (have j0 := eq2210 X0 X1
       grind)
    | exact resolve eq2210 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210
  have eq5377 : ∀ X0 X1 X2 X3 : G, (τ X0) ≠ (τ X0) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (k X0 (σ (M.op (M.op X2 (M.op X3 X3)) (τ X0)))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq169 X0 X1
       have i₂ := eq1094 X0 X2 X3
       grind)
    | exact superpose eq1094 eq169
    | (have j0 := eq169 X0 X1
       have j1 := eq1094 X0 X2 X3
       grind)
    | (have r₁ := eq169 X0 X1
       have r₂ := eq1094 X0 X1 X2
       grind)
    | exact resolve eq169 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq1094
  have eq5434 : ∀ X0 X1 X2 X3 : G, (k X0 (σ (M.op (M.op X2 (M.op X3 X3)) (τ X0)))) = X0 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq5377 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5377
  have eq55125 : ∀ X0 X1 X2 X3 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op (M.op X1 (M.op X2 X2)) (τ (σ X0)))))) ∨ (k (τ (σ X0)) X3) = (M.op (τ (σ X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq30 X0 (σ (M.op (M.op X1 (M.op X2 X2)) (τ (σ X0))))
       have i₂ := eq5434 (σ X0) X3 X1 X2
       grind)
    | exact superpose eq5434 eq30
    | (have j1 := eq5434 (σ X0) X3 X2 X3
       grind)
    | exact resolve eq30 eq5434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5434
  have eq55229 : ∀ X0 X1 X2 X3 : G, (τ (σ X0)) = (k X0 (M.op (M.op X1 (M.op X2 X2)) (τ (σ X0)))) ∨ (k (τ (σ X0)) X3) = (M.op (τ (σ X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55125 X0 X1 X2 X3
       have i₂ := eq10 (M.op (M.op X1 (M.op X2 X2)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq55125
    | (have j0 := eq55125 X0 X1 X2 X3
       grind)
    | exact resolve eq55125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55125
  have eq55283 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (k (τ (σ X0)) X3) = (M.op (τ (σ X0)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55229 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq55229
    | (have j0 := eq55229 X0 X1 X2 X3
       grind)
    | exact resolve eq55229 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55229
  have eq55310 : ∀ X0 X1 X2 X3 : G, (k X0 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 ∨ (k X0 X3) = (M.op X0 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55283 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq55283
    | (have j0 := eq55283 X0 X1 X2 X3
       grind)
    | exact resolve eq55283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55283
  have eq55693 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X0)) ≠ X0 ∨ (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X0)) = (k X0 (M.op (M.op X1 (M.op X2 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq55310 X0 X1 X2 (M.op (M.op X1 (M.op X2 X2)) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55310
  have eq55694 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X2)) X0)) = (k X0 (M.op (M.op X1 (M.op X2 X2)) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq55693 X0 X1 X2
       grind)
    | (have r₁ := eq55693 X0 X1 X2
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq55693 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55693
  have eq55732 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op X1 (M.op X2 X2)) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55694 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq55694
    | exact resolve eq55694 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55694
  have eq55770 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 (τ (M.op X1 X1))) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55732 X2 (M.op X0 (τ (M.op X1 X1))) (M.op X0 (τ (M.op X1 X1)))
       have i₂ := eq170 X1 (M.op X0 (τ (M.op X1 X1))) X0
       grind)
    | exact superpose eq170 eq55732
    | exact resolve eq55732 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq55893 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op X1 (M.op X2 X2)) (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op X1 (M.op X2 X2)) (τ X0))
       have i₂ := eq55732 (τ X0) X1 X2
       grind)
    | exact superpose eq55732 eq17
    | exact resolve eq17 eq55732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55732
  have eq55958 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op X1 (M.op X2 X2)) (τ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55893 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55893
    | exact resolve eq55893 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55893
  have eq56524 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 (τ (M.op X2 X2))) (σ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (M.op (M.op X1 (τ (M.op X2 X2))) (σ X0))
       have i₂ := eq55770 X1 X2 (σ X0)
       grind)
    | exact superpose eq55770 eq30
    | exact resolve eq30 eq55770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55770
  have eq56616 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 (τ (M.op X2 X2))) (σ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56524 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56524
    | exact resolve eq56524 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56524
  have eq57660 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op X1 (M.op X2 X2)) (τ (τ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op X1 (M.op X2 X2)) (τ (τ X0))))
       have i₂ := eq55958 (τ X0) X1 X2
       grind)
    | exact superpose eq55958 eq17
    | exact resolve eq17 eq55958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57734 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op (M.op X1 (M.op X2 X2)) (τ (τ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57660 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq57660
    | exact resolve eq57660 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57660
  have eq61442 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (M.op X1 (τ (M.op X2 X2))) (σ (σ X0)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30 X0 (τ (M.op (M.op X1 (τ (M.op X2 X2))) (σ (σ X0))))
       have i₂ := eq56616 (σ X0) X1 X2
       grind)
    | exact superpose eq56616 eq30
    | exact resolve eq30 eq56616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq61562 : ∀ X0 X1 X2 : G, (k X0 (τ (τ (M.op (M.op X1 (τ (M.op X2 X2))) (σ (σ X0)))))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61442 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61442
    | exact resolve eq61442 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61442
  have eq66473 : ∀ X0 X1 X2 X3 : G, (M.op X0 (σ X3)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 (σ X3)) = (σ (k (k (τ X0) (σ (M.op (M.op X1 (M.op X2 X2)) (τ (τ X0))))) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1734 X0 (σ (M.op (M.op X1 (M.op X2 X2)) (τ (τ X0)))) X2
       have i₂ := eq57734 X0 X1 X2
       grind)
    | exact superpose eq57734 eq1734
    | exact resolve eq1734 eq57734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734 eq57734
  have eq66619 : ∀ X0 X3 : G, (M.op X0 (σ X3)) = (σ (k (τ X0) X3)) ∨ (M.op X0 (σ X3)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq66473 X0 x x X3
       have i₂ := eq55958 (τ X0) x x
       grind)
    | exact superpose eq55958 eq66473
    | (have j0 := eq66473 X0 x x X3
       grind)
    | exact resolve eq66473 eq55958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55958 eq66473
  have eq66690 : ∀ X0 X3 : G, (k X0 (σ X3)) = (M.op X0 (σ X3)) ∨ (M.op X0 (σ X3)) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq66619 X0 X3
       have i₂ := eq17 X0 X3
       grind)
    | exact superpose eq17 eq66619
    | (have j0 := eq66619 X0 X3
       grind)
    | exact resolve eq66619 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq66619
  have eq66711 : ∀ X0 X3 : G, (M.op X0 (σ X3)) ≠ X0 ∨ (k X0 (σ X3)) = (M.op X0 (σ X3)) := by
    intro X0 X3
    first
    | (have j0 := eq66690 X0 X3
       have j1 := eq12 X0 (σ X3)
       grind)
    | (have r₁ := eq66690 X0 X3
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq66690 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66690
  have eq67526 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66711 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66711
    | exact resolve eq66711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66711
  have eq88489 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (k (σ X0) X1) = (M.op (k (σ X0) X1) (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1522 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq88529 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq88489 X0 X1 X2
       have j1 := eq12 (k (σ X0) X1) (σ X2)
       grind)
    | (have r₁ := eq88489 X0 X1 X2
       have r₂ := eq12 (k (σ X0) X1) X1
       grind)
    | exact resolve eq88489 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88489
  have eq88725 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq88529 X0 X1 X2
       have i₂ := eq29 X0 X1 X2
       grind)
    | exact superpose eq29 eq88529
    | (have j0 := eq88529 X0 X1 X2
       grind)
    | exact resolve eq88529 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq88529
  have eq88726 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq88725 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88725
  have eq89048 : ∀ X0 X1 X2 X3 : G, (σ (k X0 X3)) = (M.op (k (σ X0) (τ (M.op (M.op X1 (τ (M.op X2 X2))) (σ (σ X0))))) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq88726 X0 (τ (M.op (M.op X1 (τ (M.op X2 X2))) (σ (σ X0)))) X3
       have i₂ := eq61562 X0 X1 X2
       grind)
    | exact superpose eq61562 eq88726
    | exact resolve eq88726 eq61562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61562 eq88726
  have eq89613 : ∀ X0 X3 : G, (σ (k X0 X3)) = (M.op (σ X0) (σ X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq89048 X0 x x X3
       have i₂ := eq56616 (σ X0) x x
       grind)
    | exact superpose eq56616 eq89048
    | exact resolve eq89048 eq56616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56616 eq89048
  have eq90016 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq89613 x y
       grind)
    | exact superpose eq89613 eq16
    | exact resolve eq16 eq89613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89613
  have eq91874 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq90016
       have i₂ := eq2260 y x
       grind)
    | exact superpose eq2260 eq90016
    | (have j1 := eq2260 y x
       grind)
    | (have r₁ := eq90016
       have r₂ := eq2260 y x
       grind)
    | exact resolve eq90016 eq2260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq91875 : (M.op x y) = (M.op x x) := by grind
  clear eq91874
  have eq91879 : x ≠ (M.op x x) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq67526 y x
       have i₂ := eq91875
       grind)
    | exact superpose eq91875 eq67526
    | (have j0 := eq67526 x x
       grind)
    | exact resolve eq67526 eq91875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67526
  have eq91880 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq91875
       grind)
    | exact superpose eq91875 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq91875
       grind)
    | exact resolve eq13 eq91875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91881 : (k x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq91880
  have eq91882 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq91879
       have r₂ := eq91881
       grind)
    | exact resolve eq91879 eq91881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91879 eq91881
  have eq92409 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq90016
       have i₂ := eq91882
       grind)
    | exact superpose eq91882 eq90016
    | exact resolve eq90016 eq91882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90016 eq91882
  have eq92453 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq92409
       have i₂ := eq91875
       grind)
    | exact superpose eq91875 eq92409
    | exact resolve eq92409 eq91875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91875 eq92409
  have eq92454 : False := by grind
  exact eq92454

/-- `Equation1063`: `x = x ◇ ((y ◇ (z ◇ z)) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_Equation1063 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1063 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1063.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq61 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq61
    | exact resolve eq61 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq64
    | exact resolve eq64 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq64
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq157 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq92 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq184 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq157 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq157
    | (have j0 := eq157 X0 X1
       grind)
    | exact resolve eq157 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq157
  have eq188 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq184 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq184 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq184 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq191 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq188 X0 X1
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq188
    | (have j0 := eq188 X0 X1
       grind)
    | exact resolve eq188 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq188
  have eq578 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191
    | exact resolve eq191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq191 (σ X0) X1
       grind)
    | exact superpose eq191 eq15
    | (have j1 := eq191 (σ X0) X1
       grind)
    | exact resolve eq15 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq600 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 X1
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq589
    | (have j0 := eq589 X0 X1
       grind)
    | exact resolve eq589 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq589
  have eq615 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq578 (τ X1) X0
       grind)
    | exact superpose eq578 eq18
    | (have j1 := eq578 (τ X1) X0
       grind)
    | exact resolve eq18 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq578
  have eq1997 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq615 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq615
    | exact resolve eq615 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq2042 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1997 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1997
    | (have j0 := eq1997 X0 X1
       grind)
    | exact resolve eq1997 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997
  have eq5283 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq600 x y
       grind)
    | exact superpose eq600 eq16
    | (have j1 := eq600 x y
       grind)
    | exact resolve eq16 eq600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5342 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq600 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq5521 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5283
       have i₂ := eq2042 y x
       grind)
    | exact superpose eq2042 eq5283
    | (have j1 := eq2042 y x
       grind)
    | (have r₁ := eq5283
       have r₂ := eq2042 y x
       grind)
    | exact resolve eq5283 eq2042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5283
  have eq5522 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5521
  have eq5525 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op x x) ∨ x = (M.op y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq5522
       grind)
    | exact superpose eq5522 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq5522
       grind)
    | exact resolve eq13 eq5522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5527 : x = (M.op y x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5525
  have eq64075 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq5527
       grind)
    | exact superpose eq5527 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq5527
       grind)
    | exact resolve eq12 eq5527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5527
  have eq64076 : (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq64075
  have eq1729960 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5342 x y
       have i₂ := eq64076
       grind)
    | exact superpose eq64076 eq5342
    | (have j0 := eq5342 x y
       grind)
    | exact resolve eq5342 eq64076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64076
  have eq1730032 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1729960
  have eq1730033 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1730032
  have eq1730048 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1730033
       grind)
    | exact superpose eq1730033 eq16
    | exact resolve eq16 eq1730033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730033
  have eq1733779 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1730048
       have i₂ := eq5522
       grind)
    | exact superpose eq5522 eq1730048
    | exact resolve eq1730048 eq5522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5522 eq1730048
  have eq1733780 : (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1733779
  have eq1733808 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5342 x y
       have i₂ := eq1733780
       grind)
    | exact superpose eq1733780 eq5342
    | (have j0 := eq5342 x y
       grind)
    | exact resolve eq5342 eq1733780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5342 eq1733780
  have eq1733879 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1733808
  have eq1733880 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1733879
  have eq1738362 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1733880
       grind)
    | exact superpose eq1733880 eq16
    | exact resolve eq16 eq1733880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1738363 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq78 x (σ y)
       have i₂ := eq1733880
       grind)
    | exact superpose eq1733880 eq78
    | (have j0 := eq78 x (σ y)
       grind)
    | (have r₁ := eq78 x (σ y)
       have r₂ := eq1733880
       grind)
    | exact resolve eq78 eq1733880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1738415 : (σ (M.op x x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1738363
  have eq1738419 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1738415
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1738415
    | exact resolve eq1738415 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738415
  have eq1742131 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq1738419
       grind)
    | exact superpose eq1738419 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1738419
       grind)
    | exact resolve eq12 eq1738419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738419
  have eq1742150 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq1742131
  have eq1742166 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1742150
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1742150
    | exact resolve eq1742150 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742150
  have eq1742240 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1742166
       have i₂ := eq1733880
       grind)
    | exact superpose eq1733880 eq1742166
    | exact resolve eq1742166 eq1733880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733880 eq1742166
  have eq1742241 : (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq1742240
  have eq1743978 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2042 y x
       have i₂ := eq1742241
       grind)
    | exact superpose eq1742241 eq2042
    | (have j0 := eq2042 y x
       grind)
    | exact resolve eq2042 eq1742241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042 eq1742241
  have eq1744554 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq1743978
       have r₂ := eq1738362
       grind)
    | exact resolve eq1743978 eq1738362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743978
  have eq1746597 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1738362
       have i₂ := eq1744554
       grind)
    | exact superpose eq1744554 eq1738362
    | exact resolve eq1738362 eq1744554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1738362 eq1744554
  have eq1746608 : False := by grind
  exact eq1746608

/-- `Equation115`: `x = y ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation115 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law115 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law115.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       have i₂ := eq9 X0 (M.op X1 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq26 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq27 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq26 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq26
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq30
  have eq65 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq10
    | exact resolve eq10 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq112 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (M.op X1 X1) (τ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq18
    | exact resolve eq18 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq587 : ∀ X0 X1 X2 : G, (M.op (σ X2) (k X0 (σ X1))) ≠ (M.op (k X0 (σ X1)) (σ X2)) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (k X0 (σ X1)) (σ X2)) ∨ (k X0 (σ X1)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X0 X1 X2
       have i₂ := eq13 (σ X2) (k X0 (σ X1))
       grind)
    | exact superpose eq13 eq27
    | (have j1 := eq13 (σ X2) (k X0 (σ X1))
       grind)
    | exact resolve eq27 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (M.op X0 (τ X1)) ≠ (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq13 (τ X1) X0
       grind)
    | exact superpose eq13 eq19
    | (have j1 := eq13 X0 (τ X1)
       grind)
    | exact resolve eq19 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq797 : ∀ X0 X1 X2 : G, (M.op (k X1 (σ X2)) (σ X0)) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27 X1 X2 X0
       have i₂ := eq14 (σ X0) (k X1 (σ X2))
       grind)
    | exact superpose eq14 eq27
    | (have j1 := eq14 (k X1 (σ X2)) (σ X0)
       grind)
    | exact resolve eq27 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq799 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6373 : ∀ X0 X1 : G, (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (M.op (M.op (M.op X0 X0) (τ X1)) (τ X1)) = X0 ∨ (σ X0) = (k X1 (σ (M.op (M.op X0 X0) (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq799 X0 (M.op (M.op X0 X0) (τ X0))
       have i₂ := eq9 X0 (τ X0)
       grind)
    | exact superpose eq9 eq799
    | (have j0 := eq799 X1 (M.op (M.op X0 X0) (τ X1))
       grind)
    | exact resolve eq799 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq446624 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 ∨ (M.op (M.op (M.op X1 X1) X0) X0) = X1 ∨ (σ X1) = (k (σ X0) (σ (M.op (M.op X1 X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq6373 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6373
    | exact resolve eq6373 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6373
  have eq446978 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) X0) = X1 ∨ (M.op (M.op X1 X1) X0) = X0 ∨ (σ X1) = (σ (k X0 (M.op (M.op X1 X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq446624 X0 X1
       have i₂ := eq15 X0 (M.op (M.op X1 X1) X0)
       grind)
    | exact superpose eq15 eq446624
    | (have j0 := eq446624 X0 X1
       grind)
    | exact resolve eq446624 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446624
  have eq447311 : ∀ X0 X1 : G, (M.op (τ X1) (M.op (M.op X0 X0) (τ X1))) ≠ X0 ∨ (σ X0) = (k X1 (σ (M.op (M.op X0 X0) (τ X1)))) ∨ (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (σ X0) = (σ (k (τ X1) (M.op (M.op X0 X0) (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq589 (M.op (M.op X1 X1) (τ X1)) X1
       have i₂ := eq446978 (τ X1) X1
       grind)
    | exact superpose eq446978 eq589
    | (have j0 := eq589 (M.op (M.op X0 X0) (τ X1)) X1
       have j1 := eq446978 (τ X1) X0
       grind)
    | exact resolve eq589 eq446978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq446978
  have eq447340 : ∀ X0 X1 : G, (M.op (τ X1) (M.op (M.op X0 X0) (τ X1))) ≠ X0 ∨ (σ X0) = (k X1 (σ (M.op (M.op X0 X0) (τ X1)))) ∨ (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (σ X0) = (σ (k (τ X1) (M.op (M.op X0 X0) (τ X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq447311 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447311
  have eq447563 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (M.op (M.op X0 X0) (τ X1)))) ∨ (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (σ X0) = (σ (k (τ X1) (M.op (M.op X0 X0) (τ X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq447340 X0 X1
       grind)
    | (have r₁ := eq447340 X0 X1
       have r₂ := eq9 X0 (τ X1)
       grind)
    | exact resolve eq447340 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447340
  have eq447796 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (M.op (M.op X0 X0) (τ X1)))) ∨ (σ X0) = (k X1 (σ (M.op (M.op X0 X0) (τ X1)))) ∨ (τ X1) = (M.op (M.op X0 X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq447563 X0 X1
       have i₂ := eq19 X1 (M.op (M.op X0 X0) (τ X1))
       grind)
    | exact superpose eq19 eq447563
    | (have j0 := eq447563 X0 X1
       grind)
    | exact resolve eq447563 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447563
  have eq447797 : ∀ X0 X1 : G, (τ X1) = (M.op (M.op X0 X0) (τ X1)) ∨ (σ X0) = (k X1 (σ (M.op (M.op X0 X0) (τ X1)))) := by
    intro X0 X1
    first
    | (have j0 := eq447796 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447796
  have eq448267 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = X0 ∨ (σ X1) = (k (σ X0) (σ (M.op (M.op X1 X1) X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq447797 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq447797
    | exact resolve eq447797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447797
  have eq448621 : ∀ X0 X1 : G, (σ X1) = (σ (k X0 (M.op (M.op X1 X1) X0))) ∨ (M.op (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq448267 X0 X1
       have i₂ := eq15 X0 (M.op (M.op X1 X1) X0)
       grind)
    | exact superpose eq15 eq448267
    | (have j0 := eq448267 X0 X1
       grind)
    | exact resolve eq448267 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448267
  have eq456330 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (k X1 (M.op (τ (M.op X0 X0)) X1))) ∨ (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq448621 X0 (τ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq448621
    | exact resolve eq448621 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448621
  have eq456970 : ∀ X0 X1 : G, (σ (k X1 (M.op (τ (M.op X0 X0)) X1))) = X0 ∨ (M.op (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456330 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq456330
    | (have j0 := eq456330 X0 X1
       grind)
    | exact resolve eq456330 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456330
  have eq464430 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (τ (M.op X1 X1))) = X0 ∨ (σ (k (M.op (M.op X0 X0) (τ (M.op X1 X1))) X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq456970 X0 (M.op (M.op X0 X0) (τ (M.op X0 X0)))
       have i₂ := eq9 X0 (τ (M.op X0 X0))
       grind)
    | exact superpose eq9 eq456970
    | exact resolve eq456970 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456970
  have eq755632 : ∀ X0 X1 : G, (σ (k (M.op (M.op X0 X0) (τ (M.op X1 X1))) X0)) = X1 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq112 X1 X0
       have i₂ := eq464430 X0 X1
       grind)
    | exact superpose eq464430 eq112
    | (have j1 := eq464430 X0 X1
       grind)
    | exact resolve eq112 eq464430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq464430
  have eq756012 : ∀ X0 X1 : G, (σ (k (M.op (τ (M.op X0 X0)) (τ (M.op X1 X1))) (τ X0))) = X1 ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq755632 (τ X0) X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq755632
    | exact resolve eq755632 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq756022 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op (M.op X1 X1) (τ (σ (M.op X0 X0)))) X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq755632 X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq755632
    | (have j0 := eq755632 X1 (σ X0)
       grind)
    | exact resolve eq755632 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755632
  have eq756726 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op (M.op X1 X1) (M.op X0 X0)) X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq756022 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq756022
    | (have j0 := eq756022 X0 X1
       grind)
    | exact resolve eq756022 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756022
  have eq756731 : ∀ X0 X1 : G, (k (σ (M.op (τ (M.op X0 X0)) (τ (M.op X1 X1)))) X0) = X1 ∨ (τ X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq756012 X0 X1
       have i₂ := eq20 X0 (M.op (τ (M.op X0 X0)) (τ (M.op X1 X1)))
       grind)
    | exact superpose eq20 eq756012
    | (have j0 := eq756012 X0 X1
       grind)
    | exact resolve eq756012 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq756012
  have eq756826 : ∀ X0 X1 : G, (σ X0) = (σ (k (M.op (M.op X1 X1) (M.op X0 X0)) X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq756726 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq756726
    | (have j0 := eq756726 X0 X1
       grind)
    | exact resolve eq756726 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756726
  have eq757189 : ∀ X0 X1 : G, (τ (σ X0)) = (k (M.op (M.op X1 X1) (M.op X0 X0)) X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (M.op (M.op X1 X1) (M.op X0 X0)) X1)
       have i₂ := eq756826 X0 X1
       grind)
    | exact superpose eq756826 eq10
    | (have j1 := eq756826 X0 X1
       grind)
    | exact resolve eq10 eq756826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756826
  have eq757567 : ∀ X0 X1 : G, (k (M.op (M.op X1 X1) (M.op X0 X0)) X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq757189 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq757189
    | (have j0 := eq757189 X0 X1
       grind)
    | exact resolve eq757189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757189
  have eq1354347 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) ≠ (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (k X1 (σ X2)) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq587 X1 X2 X0
       have i₂ := eq797 X0 X1 X2
       grind)
    | exact superpose eq797 eq587
    | (have j0 := eq587 X1 X2 X0
       have j1 := eq797 X0 X1 X2
       grind)
    | (have r₁ := eq587 X1 X2 X0
       have r₂ := eq797 X0 X1 X2
       grind)
    | exact resolve eq587 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq797
  have eq1355500 : ∀ X0 X1 X2 : G, (M.op (σ X0) (k X1 (σ X2))) ≠ (M.op (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1354347 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354347
  have eq1355501 : ∀ X0 X1 X2 : G, (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) ∨ (σ X0) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1355500 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355500
  have eq1357241 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op (σ (τ X0)) (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 (k (τ X1) X2)
       have i₂ := eq1355501 (τ X0) X1 X2
       grind)
    | exact superpose eq1355501 eq19
    | (have j1 := eq1355501 (τ X0) X1 X2
       grind)
    | exact resolve eq19 eq1355501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355501
  have eq1357734 : ∀ X0 X1 X2 : G, (k X0 (σ (k (τ X1) X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1357241 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1357241
    | (have j0 := eq1357241 X0 X1 X2
       grind)
    | exact resolve eq1357241 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357241
  have eq1358081 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (σ (τ X0)) = (k X1 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1357734 X0 X1 X2
       have i₂ := eq19 X1 X2
       grind)
    | exact superpose eq19 eq1357734
    | (have j0 := eq1357734 X0 X1 X2
       grind)
    | exact resolve eq1357734 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357734
  have eq1358312 : ∀ X0 X1 X2 : G, (k X0 (k X1 (σ X2))) = (M.op X0 (k X1 (σ X2))) ∨ (k X1 (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1358081 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1358081
    | (have j0 := eq1358081 X0 X1 X2
       grind)
    | exact resolve eq1358081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358081
  have eq1358746 : ∀ X0 X1 X2 : G, (k X1 (k X2 X0)) = (M.op X1 (k X2 X0)) ∨ (k X2 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1358312 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1358312
    | exact resolve eq1358312 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1359008 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (τ X0) = (τ (M.op (σ X2) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1358312 X0 (σ (M.op (τ (M.op (σ X2) (σ X2))) (τ (M.op X1 X1)))) X2
       have i₂ := eq756731 (σ X2) X1
       grind)
    | exact superpose eq756731 eq1358312
    | (have j1 := eq756731 (σ X2) X0
       grind)
    | exact resolve eq1358312 eq756731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756731 eq1358312
  have eq1360543 : ∀ X0 X1 X2 : G, (τ X0) = (τ (σ (M.op X2 X2))) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1359008 X0 X1 X2
       have i₂ := eq23 X2
       grind)
    | exact superpose eq23 eq1359008
    | (have j0 := eq1359008 X0 X1 X2
       grind)
    | exact resolve eq1359008 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359008
  have eq1360642 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (M.op X2 X2) ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1360543 X0 X1 X2
       have i₂ := eq10 (M.op X2 X2)
       grind)
    | exact superpose eq10 eq1360543
    | (have j0 := eq1360543 X0 X1 X2
       grind)
    | exact resolve eq1360543 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360543
  have eq1360916 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 ∨ (M.op X2 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1358746 X1 X1 (M.op (M.op X1 X1) (M.op X0 X0))
       have i₂ := eq757567 X0 X1
       grind)
    | exact superpose eq757567 eq1358746
    | (have j0 := eq1358746 X0 (M.op X1 X0) X1
       have j1 := eq757567 X0 X2
       grind)
    | exact resolve eq1358746 eq757567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757567 eq1358746
  have eq1364202 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq1360916 X1 (τ X0) X2
       grind)
    | exact superpose eq1360916 eq19
    | (have j1 := eq1360916 (k X0 (σ X1)) (σ (M.op (τ X0) X1)) X2
       grind)
    | exact resolve eq19 eq1360916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1360916
  have eq1372236 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (M.op X2 X2) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1360642 (σ X1) (σ X0) X2
       grind)
    | exact superpose eq1360642 eq15
    | (have j1 := eq1360642 (σ X1) (σ X0) X2
       grind)
    | exact resolve eq15 eq1360642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360642
  have eq1373102 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1372236 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1372236
    | (have j0 := eq1372236 X0 X1 X2
       grind)
    | exact resolve eq1372236 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372236
  have eq1496888 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1364202 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1364202
    | (have j0 := eq1364202 X0 X1 X2
       grind)
    | exact resolve eq1364202 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364202
  have eq1497668 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1496888 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1496888
    | (have j0 := eq1496888 X0 X1 X2
       grind)
    | exact resolve eq1496888 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496888
  have eq1614848 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1373102 x y X0
       grind)
    | exact superpose eq1373102 eq16
    | (have j1 := eq1373102 x y X0
       grind)
    | exact resolve eq16 eq1373102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373102
  have eq1616266 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1614848 X0
       have i₂ := eq1497668 x y X1
       grind)
    | exact superpose eq1497668 eq1614848
    | (have j0 := eq1614848 X0
       have j1 := eq1497668 (M.op X0 X0) y X0
       grind)
    | (have r₁ := eq1614848 X0
       have r₂ := eq1497668 x y x
       grind)
    | (have r₁ := eq1614848 X0
       have r₂ := eq1497668 (σ (M.op x y)) (σ (k x y)) x
       grind)
    | (have r₁ := eq1614848 X0
       have r₂ := eq1497668 (σ (k x y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq1614848 eq1497668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497668 eq1614848
  have eq1616291 : ∀ X0 X1 : G, x = y ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1616266 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616266
  have eq1616317 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1616291 X0 X1
       grind)
    | exact superpose eq1616291 eq16
    | (have j1 := eq1616291 X0 X0
       grind)
    | exact resolve eq16 eq1616291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616291
  have eq1616320 : ∀ X0 X1 : G, (σ x) = (σ y) ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1616317 X0 X0
       grind)
    | (have r₁ := eq1616317 X0 X1
       have r₂ := eq23 x
       grind)
    | exact resolve eq1616317 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616317
  have eq1616322 : ∀ X0 X1 : G, y = (τ (σ x)) ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 y
       have i₂ := eq1616320 X0 X1
       grind)
    | exact superpose eq1616320 eq10
    | (have j1 := eq1616320 X0 X0
       grind)
    | exact resolve eq10 eq1616320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616320
  have eq1616828 : ∀ X0 X1 : G, x = y ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1616322 X0 X1
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1616322
    | (have j0 := eq1616322 X0 X0
       grind)
    | exact resolve eq1616322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616322
  have eq1616830 : ∀ X0 X1 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1616828 X0 X1
       grind)
    | exact superpose eq1616828 eq16
    | (have j1 := eq1616828 X0 X0
       grind)
    | exact resolve eq16 eq1616828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616828
  have eq1616833 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ y = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1616830 X0 X0
       grind)
    | (have r₁ := eq1616830 X0 X1
       have r₂ := eq23 x
       grind)
    | exact resolve eq1616830 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1616830
  have eq1618536 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq1616833 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616833
  have eq1618537 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq1618536 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618536
  have eq1619840 : ∀ X0 : G, (M.op (M.op X0 X0) y) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq1618537 (M.op X0 X0)
       grind)
    | exact superpose eq1618537 eq9
    | exact resolve eq9 eq1618537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1620587 : ∀ X0 : G, (M.op y y) = X0 := by
    intro X0
    first
    | (have i₁ := eq1619840 X0
       have i₂ := eq1618537 X0
       grind)
    | exact superpose eq1618537 eq1619840
    | exact resolve eq1619840 eq1618537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1619840
  have eq1621998 : ∀ X0 : G, y = X0 := by
    intro X0
    first
    | (have i₁ := eq1620587 X0
       have i₂ := eq1618537 y
       grind)
    | exact superpose eq1618537 eq1620587
    | exact resolve eq1620587 eq1618537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618537 eq1620587
  have eq1626290 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1621998 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq1621998 eq16
    | exact resolve eq16 eq1621998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1637287 : False := by grind
  exact eq1637287

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_Equation1242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq264 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq264 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq264 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq264 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq276 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq265 (σ X0)
       grind)
    | exact superpose eq265 eq15
    | exact resolve eq15 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq282 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq265 (τ X0)
       grind)
    | exact superpose eq265 eq31
    | exact resolve eq31 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq282
    | exact resolve eq282 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq295 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq265 X0
       grind)
    | exact superpose eq265 eq276
    | exact resolve eq276 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq276
  have eq402 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq402 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq415 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq414 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq438 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq415 X0 (τ X1)
       grind)
    | exact superpose eq415 eq18
    | (have j1 := eq415 X0 (τ X1)
       grind)
    | exact resolve eq18 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq441 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq415 (σ X0) (σ X1)
       grind)
    | exact superpose eq415 eq15
    | (have j1 := eq415 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq464 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq441 X0 X1
       have i₂ := eq295 X0
       grind)
    | exact superpose eq295 eq441
    | (have j0 := eq441 X0 X1
       grind)
    | exact resolve eq441 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq469 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq438
    | exact resolve eq438 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq503 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq469
    | (have j0 := eq469 X0 X1
       grind)
    | exact resolve eq469 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq799 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq464 x y
       grind)
    | exact superpose eq464 eq16
    | (have j1 := eq464 x y
       grind)
    | exact resolve eq16 eq464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq813 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq464 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq827 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq799
       have i₂ := eq503 y x
       grind)
    | exact superpose eq503 eq799
    | (have j1 := eq503 y x
       grind)
    | (have r₁ := eq799
       have r₂ := eq503 y x
       grind)
    | exact resolve eq799 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503 eq799
  have eq828 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq827
  have eq833 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq828
       grind)
    | exact superpose eq828 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq828
       grind)
    | exact resolve eq13 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq836 : x = (M.op y x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq833
  have eq844 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq813 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq813
    | (have j0 := eq813 (τ X0) (τ X1)
       grind)
    | exact resolve eq813 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq860 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 X1
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq844
    | (have j0 := eq844 X0 X1
       grind)
    | exact resolve eq844 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq844
  have eq868 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq860 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq860
    | (have j0 := eq860 X0 X1
       grind)
    | exact resolve eq860 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq876 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq868 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq868
    | (have j0 := eq868 X0 X1
       grind)
    | exact resolve eq868 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq880 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq876 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq876
    | (have j0 := eq876 X0 X1
       grind)
    | exact resolve eq876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876
  have eq883 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq880 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq880
    | (have j0 := eq880 X0 X1
       grind)
    | exact resolve eq880 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq884 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (M.op X0 X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq883 X0 X1
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq883
    | (have j0 := eq883 X0 X1
       grind)
    | exact resolve eq883 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289 eq883
  have eq885 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq884 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq884
    | (have j0 := eq884 X0 X1
       grind)
    | exact resolve eq884 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884
  have eq9322 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq836
       grind)
    | exact superpose eq836 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq836
       grind)
    | exact resolve eq12 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq9327 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
  clear eq9322
  have eq50541 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9327
       grind)
    | exact superpose eq9327 eq16
    | exact resolve eq16 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9327
  have eq50598 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq50541
       have i₂ := eq828
       grind)
    | exact superpose eq828 eq50541
    | exact resolve eq50541 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828 eq50541
  have eq50603 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq50598
  have eq50604 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq50603
  have eq50618 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq50604
       grind)
    | exact superpose eq50604 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq50604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50652 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq50618
       have r₂ := eq295 x
       grind)
    | exact resolve eq50618 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50618
  have eq50659 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq50652
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq50652
    | exact resolve eq50652 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50652
  have eq50664 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq50659
       have i₂ := eq295 x
       grind)
    | exact superpose eq295 eq50659
    | exact resolve eq50659 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq50659
  have eq103397 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq50664
       grind)
    | exact superpose eq50664 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq50664
       grind)
    | exact resolve eq12 eq50664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50664
  have eq103434 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by grind
  clear eq103397
  have eq103468 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq103434
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq103434
    | exact resolve eq103434 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103434
  have eq832608 : (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq50604
       have i₂ := eq103468
       grind)
    | exact superpose eq103468 eq50604
    | exact resolve eq50604 eq103468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50604 eq103468
  have eq832805 : (k x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq832608
  have eq833028 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq813 x y
       have i₂ := eq832805
       grind)
    | exact superpose eq832805 eq813
    | (have j0 := eq813 x y
       grind)
    | (have r₁ := eq813 x y
       have r₂ := eq832805
       grind)
    | exact resolve eq813 eq832805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833031 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq885 x y
       have i₂ := eq832805
       grind)
    | exact superpose eq832805 eq885
    | (have j0 := eq885 x y
       grind)
    | (have r₁ := eq885 x y
       have r₂ := eq832805
       grind)
    | exact resolve eq885 eq832805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832805
  have eq833241 : (M.op x y) = (M.op x x) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq833031
  have eq833243 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq833028
  have eq833268 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have j1 := eq813 x y
       grind)
    | (have r₁ := eq833243
       have r₂ := eq813 x y
       grind)
    | exact resolve eq833243 eq813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813 eq833243
  have eq833275 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq833268
       grind)
    | exact superpose eq833268 eq16
    | exact resolve eq16 eq833268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833268
  have eq834356 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq833275
       have i₂ := eq833241
       grind)
    | exact superpose eq833241 eq833275
    | exact resolve eq833275 eq833241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833241
  have eq834425 : (σ (k x y)) = (σ (M.op x x)) := by grind
  clear eq834356
  have eq834501 : (k x y) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq834425
       grind)
    | exact superpose eq834425 eq10
    | exact resolve eq10 eq834425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834425
  have eq834898 : (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq834501
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq834501
    | exact resolve eq834501 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834501
  have eq835024 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq885 x y
       have i₂ := eq834898
       grind)
    | exact superpose eq834898 eq885
    | (have j0 := eq885 x y
       grind)
    | (have r₁ := eq885 x y
       have r₂ := eq834898
       grind)
    | exact resolve eq885 eq834898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq834898
  have eq835234 : (M.op x y) = (M.op x x) := by grind
  clear eq835024
  have eq835307 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq833275
       have i₂ := eq835234
       grind)
    | exact superpose eq835234 eq833275
    | exact resolve eq833275 eq835234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833275 eq835234
  have eq835376 : False := by grind
  exact eq835376

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyx_pxy_Equation1242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq264 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq12 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq269 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq274 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq265 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq265 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq265 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq275 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq269 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq269 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq269 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq269 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269
  have eq286 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq274 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq274
    | (have j0 := eq274 X0 X1
       grind)
    | exact resolve eq274 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq287 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq286 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq288 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq275
    | (have j0 := eq275 X0 X1
       grind)
    | exact resolve eq275 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq289 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq288 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq294 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq289 X0 X1
       have j1 := eq287 X0 X1
       grind)
    | (have r₁ := eq289 X0 X1
       have r₂ := eq287 X0 X1
       grind)
    | exact resolve eq289 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq289
  have eq295 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq294 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq294
    | exact resolve eq294 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq306 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq294 x y
       grind)
    | exact superpose eq294 eq16
    | exact resolve eq16 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq403 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq295 X0 (τ X1)
       grind)
    | exact superpose eq295 eq18
    | exact resolve eq18 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq295
  have eq432 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq403
    | exact resolve eq403 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq446 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq432 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq432
    | exact resolve eq432 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq485 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq306
       have i₂ := eq446 x y
       grind)
    | exact superpose eq446 eq306
    | exact resolve eq306 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq446
  have eq486 : False := by grind
  exact eq486
