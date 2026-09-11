import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pxy_x_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
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
  have eq175 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq178
    | exact resolve eq178 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq175 eq178
    | exact resolve eq178 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq176 eq178
    | exact resolve eq178 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq178 X0 x X3
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq178 x x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq178
    | exact resolve eq178 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq176 eq543
    | exact resolve eq543 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq543
  have eq577 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq175 eq542
    | exact resolve eq542 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq542
  have eq578 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq541 X0 X1 x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq541
    | exact resolve eq541 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq597 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq578 X0 x
       have i₂ := eq178 X0 x X1
       grind)
    | (have i₁ := eq578 x x
       have i₂ := eq178 x X1 x
       grind)
    | exact superpose eq178 eq578
    | exact resolve eq578 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq1033 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : (M.op x y) = (k x y) ∨ y = (M.op y y) := by
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
  have eq1079 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq1083 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1090 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1072
       grind)
    | exact superpose eq1072 eq41
    | exact resolve eq41 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq1091 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1090
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1090
    | exact resolve eq1090 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1090
  have eq1093 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1091
    | exact resolve eq1091 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1103 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1093 eq1079
    | exact resolve eq1079 eq1093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1079 eq1093
  have eq1110 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1103
       have r₂ := eq27
       grind)
    | exact resolve eq1103 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103
  have eq1126 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1110 eq179
    | exact resolve eq179 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1137 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1110 eq1126
    | exact resolve eq1126 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110 eq1126
  have eq1152 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1137 eq153
    | exact resolve eq153 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1137
  have eq1155 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq32 eq1152
    | exact resolve eq1152 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1152
  have eq1158 : y = (M.op y y) := by
    first
    | (have j1 := eq1083 y
       grind)
    | (have r₁ := eq1155
       have r₂ := eq1083 y
       grind)
    | exact resolve eq1155 eq1083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155
  have eq1172 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X0 X1 y
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq178
    | exact resolve eq178 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1173 : (k y y) = (M.op y y) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq179
    | exact resolve eq179 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq180 y
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq180
    | exact resolve eq180 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1177 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1 y
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq548
    | exact resolve eq548 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq1182 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1174
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1174
    | exact resolve eq1174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1183 : y = (k y y) := by
    first
    | (have i₁ := eq1173
       have i₂ := eq1158
       grind)
    | exact superpose eq1158 eq1173
    | exact resolve eq1173 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158 eq1173
  have eq1188 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1182 eq577
    | exact resolve eq577 eq1182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq1182
  have eq1200 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1183
       grind)
    | exact superpose eq1183 eq41
    | exact resolve eq41 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq1183
  have eq1203 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1200
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1200
    | exact resolve eq1200 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1200
  have eq1206 : x = (k (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1188 eq28
    | (have j0 := eq28 x x
       grind)
    | exact resolve eq28 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1188
  have eq1240 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1203 eq1083
    | (have j0 := eq1083 (σ y)
       grind)
    | (have r₁ := eq1083 (σ y)
       have r₂ := eq1203
       grind)
    | exact resolve eq1083 eq1203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1203
  have eq1241 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1240
  have eq1256 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1241 eq178
    | exact resolve eq178 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1259 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1241 eq182
    | exact resolve eq182 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1264 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq1241 eq597
    | exact resolve eq597 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq1241
  have eq1268 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq1259
    | exact resolve eq1259 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1277 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq1268 eq576
    | exact resolve eq576 eq1268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1493 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq1264 eq16
    | exact resolve eq16 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1503 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) X0) y) := by
    intro X0
    first
    | (have i₁ := eq1493 X0 x
       have i₂ := eq1177 (M.op (M.op X0 sF3) X0) x
       grind)
    | exact superpose eq1177 eq1493
    | exact resolve eq1493 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1513 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq1264 eq1503
    | exact resolve eq1503 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq1503
  have eq3964 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1206 eq38
    | exact resolve eq38 eq1206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq1206
  have eq3970 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3964
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3964
    | exact resolve eq3964 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3964
  have eq4248 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq3970 eq1033
    | (have j0 := eq1033 X0 (σ x) x
       grind)
    | exact resolve eq1033 eq3970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq4249 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4248 x
       have i₂ := eq1177 (M.op sF1 sF2) x
       grind)
    | exact superpose eq1177 eq4248
    | exact resolve eq4248 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq4248
  have eq4253 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4249
       have i₂ := eq1513 (M.op sF1 sF2)
       grind)
    | exact superpose eq1513 eq4249
    | exact resolve eq4249 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513 eq4249
  have eq4255 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq4253
    | (have j1 := eq28 x (σ x)
       grind)
    | exact resolve eq4253 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4253
  have eq4256 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3970 eq4255
    | exact resolve eq4255 eq3970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3970 eq4255
  have eq4257 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq4256
    | exact resolve eq4256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4256
  have eq4258 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq4257
       have r₂ := eq27
       grind)
    | exact resolve eq4257 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4257
  have eq4374 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4258 eq1256
    | exact resolve eq1256 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4376 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq4374
    | exact resolve eq4374 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4374
  have eq4405 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4258 eq4376
    | exact resolve eq4376 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4258 eq4376
  have eq4447 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 x
       have i₂ := eq4405
       grind)
    | exact superpose eq4405 eq179
    | exact resolve eq179 eq4405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4500 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4405 eq4447
    | exact resolve eq4447 eq4405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4405 eq4447
  have eq4735 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4500
       grind)
    | exact superpose eq4500 eq40
    | exact resolve eq40 eq4500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4500
  have eq4740 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4735
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4735
    | exact resolve eq4735 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4735
  have eq5060 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4740 eq1083
    | (have j0 := eq1083 (σ x)
       grind)
    | (have r₁ := eq1083 (σ x)
       have r₂ := eq4740
       grind)
    | exact resolve eq1083 eq4740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4740
  have eq5062 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5060
  have eq5374 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5062 eq1256
    | exact resolve eq1256 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq5376 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5374
    | exact resolve eq5374 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5374
  have eq5406 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5062 eq5376
    | exact resolve eq5376 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5062 eq5376
  have eq5407 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5406
  have eq5435 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5407 eq27
    | exact resolve eq27 eq5407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq5438 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
    first
    | exact superpose eq5407 eq576
    | exact resolve eq576 eq5407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq5443 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5407 eq1277
    | exact resolve eq1277 eq5407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1277 eq5407
  have eq5450 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq5438
       have i₂ := eq179 sF2
       grind)
    | exact superpose eq179 eq5438
    | exact resolve eq5438 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq5438
  have eq5454 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5443 eq5450
    | exact resolve eq5450 eq5443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5443 eq5450
  have eq5583 : (τ (σ x)) = (k (τ (σ x)) x) := by
    first
    | exact superpose eq5454 eq142
    | exact resolve eq142 eq5454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq5454
  have eq5591 : x = (k x x) := by
    first
    | exact superpose eq30 eq5583
    | exact resolve eq5583 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq5583
  have eq5652 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1083 x
       have i₂ := eq5591
       grind)
    | exact superpose eq5591 eq1083
    | (have j0 := eq1083 x
       grind)
    | (have r₁ := eq1083 x
       have r₂ := eq5591
       grind)
    | exact resolve eq1083 eq5591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq5591
  have eq5655 : x = (M.op x x) := by grind
  clear eq5652
  have eq5699 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1172 x x
       have i₂ := eq5655
       grind)
    | exact superpose eq5655 eq1172
    | exact resolve eq1172 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq5703 : x = (M.op x y) := by
    first
    | (have i₁ := eq5699
       have i₂ := eq5655
       grind)
    | exact superpose eq5655 eq5699
    | exact resolve eq5699 eq5655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5655 eq5699
  have eq5732 : x = (M.op x y) := by
    first
    | (have i₁ := eq5703
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5703
    | exact resolve eq5703 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5703
  have eq5783 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5732
       grind)
    | exact superpose eq5732 eq22
    | exact resolve eq22 eq5732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5732
  have eq5834 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5783 eq20
    | exact resolve eq20 eq5783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5783
  have eq5853 : False := by grind
  exact eq5853

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_x_y_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq43 : ∀ X0 X1 : G, (σ (k (k x X0) X1)) = (k (k (σ x) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k x X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
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
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq174 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X1 : G, (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq175 eq177
    | exact resolve eq177 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq177 (M.op X0 (M.op X0 X1)) X2 x
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       have i₂ := eq177 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq180 sF2
       have i₂ := eq177 sF2 sF2 x
       grind)
    | (have i₁ := eq180 x
       have i₂ := eq177 sF2 x x
       grind)
    | exact superpose eq177 eq180
    | exact resolve eq180 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq175 eq541
    | exact resolve eq541 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq575 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq174 eq540
    | exact resolve eq540 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq576 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1 x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq539
    | exact resolve eq539 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq595 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq576 X0 x
       have i₂ := eq177 X0 x X1
       grind)
    | (have i₁ := eq576 x x
       have i₂ := eq177 x X1 x
       grind)
    | exact superpose eq177 eq576
    | exact resolve eq576 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq1036 : x ≠ x ∨ x = (M.op x x) ∨ x = (k (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq575 eq12
    | (have j0 := eq12 (M.op x (M.op x y)) x
       grind)
    | (have r₁ := eq12 (M.op x (M.op x y)) x
       have r₂ := eq575
       grind)
    | exact resolve eq12 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq1038 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq1041 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1045 : x = (k (M.op x (M.op x y)) x) ∨ x = (M.op x x) := by grind
  clear eq1036
  have eq1062 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq1065 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1068 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1128 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1142 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1068 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq1162 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1142 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq1142 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq1142 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1142 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142
  have eq1166 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1128 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1128
    | (have j0 := eq1128 (σ X0)
       grind)
    | exact resolve eq1128 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1162 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1162
    | (have j0 := eq1162 (σ X0) X1
       grind)
    | exact resolve eq1162 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1177 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1062
       grind)
    | exact superpose eq1062 eq40
    | exact resolve eq40 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq1178 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1177
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1177
    | exact resolve eq1177 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1180 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1178
    | exact resolve eq1178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1180 eq1065
    | exact resolve eq1065 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065 eq1180
  have eq1280 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1273
       have r₂ := eq27
       grind)
    | exact resolve eq1273 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1285 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1280 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1280
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1280
       grind)
    | exact resolve eq13 eq1280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1304 : ∀ X0 : G, y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq1285 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1285
  have eq1319 : ∀ X0 X1 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1304 X1
       grind)
    | exact superpose eq1304 eq13
    | (have j0 := eq13 X0 y
       have j1 := eq1304 X1
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1304 X0
       grind)
    | exact resolve eq13 eq1304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq1338 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1319 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1388 : ∀ X0 : G, (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq107 X0
       have i₂ := eq1338 (k sF3 X0) x
       grind)
    | exact superpose eq1338 eq107
    | (have j1 := eq1338 X0 x
       grind)
    | exact resolve eq107 eq1338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1338
  have eq1396 : ∀ X0 : G, y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq31 eq1388
    | (have j0 := eq1388 y
       grind)
    | exact resolve eq1388 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1410 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1396 X0
       have j1 := eq1162 y X0
       grind)
    | (have r₁ := eq1396 X0
       have r₂ := eq1162 y x
       grind)
    | (have r₁ := eq1396 y
       have r₂ := eq1162 y x
       grind)
    | exact resolve eq1396 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1417 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1168 y X0
       have i₂ := eq1410 y
       grind)
    | exact superpose eq1410 eq1168
    | (have j0 := eq1168 y X0
       grind)
    | exact resolve eq1168 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1128 y
       have i₂ := eq1410 y
       grind)
    | exact superpose eq1410 eq1128
    | (have j0 := eq1128 y
       grind)
    | (have r₁ := eq1128 y
       have r₂ := eq1410 y
       grind)
    | exact resolve eq1128 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1424 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq1410 y
       grind)
    | exact superpose eq1410 eq36
    | exact resolve eq36 eq1410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1410
  have eq1430 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1419
  have eq1432 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1417 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1438 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1424
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1424
    | exact resolve eq1424 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424
  have eq1442 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1432 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1432
    | (have j0 := eq1432 X0
       grind)
    | exact resolve eq1432 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1432
  have eq1452 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq1430
       grind)
    | exact superpose eq1430 eq178
    | exact resolve eq178 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1454 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 y
       have i₂ := eq1430
       grind)
    | exact superpose eq1430 eq180
    | exact resolve eq180 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1475 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1452
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1452
    | exact resolve eq1452 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452
  have eq1485 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1438 eq1128
    | (have j0 := eq1128 (σ y)
       grind)
    | (have r₁ := eq1128 (σ y)
       have r₂ := eq1438
       grind)
    | exact resolve eq1128 eq1438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq1438
  have eq1486 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1485
  have eq1534 : x = (k (M.op x y) x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1475 eq1045
    | exact resolve eq1045 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1555 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1486 eq177
    | exact resolve eq177 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1558 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1486 eq180
    | exact resolve eq180 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1564 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1486 eq595
    | exact resolve eq595 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1566 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1486 eq177
    | exact resolve eq177 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq1575 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1486 eq1566
    | exact resolve eq1566 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1579 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1558
    | exact resolve eq1558 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558
  have eq1606 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1579 eq574
    | exact resolve eq574 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq1609 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1579 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq1579
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1579
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1579
       grind)
    | exact resolve eq12 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1615 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1609
  have eq1673 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1126 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1126
    | (have j0 := eq1126 (σ X0) (σ X1)
       grind)
    | exact resolve eq1126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1916 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1454 eq1579
    | exact resolve eq1579 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579
  have eq1926 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1916
  have eq2323 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 (σ y)) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1564 eq12
    | (have j0 := eq12 (M.op X0 (σ y)) X0
       grind)
    | (have r₁ := eq12 (M.op X0 (σ y)) X0
       have r₂ := eq1564 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1564 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1564 X0
       grind)
    | exact resolve eq12 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq2338 : ∀ X0 : G, (k (M.op X0 (σ y)) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2323
  have eq8092 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1534 eq37
    | exact resolve eq37 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq8100 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8092
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8092
    | exact resolve eq8092 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8092
  have eq8846 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8100 eq1126
    | (have j0 := eq1126 (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq1126 (σ (M.op x y)) (σ x)
       have r₂ := eq8100
       grind)
    | exact resolve eq1126 eq8100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8847 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8846
  have eq30031 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8847 eq1555
    | exact resolve eq1555 eq8847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30032 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq30031
  have eq30090 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq30032
    | exact resolve eq30032 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30032
  have eq30136 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq8847 eq30090
    | exact resolve eq30090 eq8847
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8847 eq30090
  have eq30172 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (M.op (M.op (σ (M.op x y)) (σ x)) X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30136 eq569
    | exact resolve eq569 eq30136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq30191 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq30136 eq30172
    | exact resolve eq30172 eq30136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30136 eq30172
  have eq30198 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq573 eq30191
    | (have j0 := eq30191 (σ y)
       grind)
    | exact resolve eq30191 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq30191
  have eq30201 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1454 eq30198
    | exact resolve eq30198 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454 eq30198
  have eq30203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1926 eq30201
    | exact resolve eq30201 eq1926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1926 eq30201
  have eq30205 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq30203
       have r₂ := eq27
       grind)
    | exact resolve eq30203 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30203
  have eq30209 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq30205
       grind)
    | exact superpose eq30205 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq30205
       grind)
    | exact resolve eq13 eq30205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30205
  have eq30349 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq30209 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30209
  have eq30588 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq30349 x
       grind)
    | exact superpose eq30349 eq35
    | exact resolve eq35 eq30349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30349
  have eq30628 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30588
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30588
    | exact resolve eq30588 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30588
  have eq31623 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30628 eq1126
    | (have j0 := eq1126 (σ x) (σ x)
       grind)
    | (have r₁ := eq1126 (σ x) (σ x)
       have r₂ := eq30628
       grind)
    | exact resolve eq1126 eq30628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30628
  have eq31624 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq31623
  have eq31625 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq31624
  have eq32952 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31625 eq1555
    | exact resolve eq1555 eq31625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1555
  have eq32953 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq32952
  have eq33012 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq32953
    | exact resolve eq32953 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32953
  have eq33067 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31625 eq33012
    | exact resolve eq33012 eq31625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31625 eq33012
  have eq33068 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33067
  have eq33092 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq33068 eq175
    | exact resolve eq175 eq33068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33096 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33068 eq1041
    | (have r₁ := eq1041
       have r₂ := eq33068
       grind)
    | exact resolve eq1041 eq33068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33099 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq33100 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33096
  have eq33103 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1486 eq33100
    | exact resolve eq33100 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33100
  have eq33107 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq33092
    | (have j0 := eq33092 X0
       grind)
    | exact resolve eq33092 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33092
  have eq33113 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq33068 eq33107
    | exact resolve eq33107 eq33068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33068 eq33107
  have eq38124 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33103 eq90
    | exact resolve eq90 eq33103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38144 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq38124
    | exact resolve eq38124 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38124
  have eq38262 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq38144 eq33113
    | exact resolve eq33113 eq38144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33113
  have eq38283 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq38262
  have eq38372 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | (have r₁ := eq38283
       have r₂ := eq33099
       grind)
    | exact resolve eq38283 eq33099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38283
  have eq38682 : (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k x y) := by
    first
    | exact superpose eq38372 eq38144
    | exact resolve eq38144 eq38372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38144 eq38372
  have eq38900 : (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq38682
  have eq38933 : y = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq38900
       have r₂ := eq33099
       grind)
    | exact resolve eq38900 eq33099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38900
  have eq38951 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq38933
       grind)
    | exact superpose eq38933 eq1062
    | exact resolve eq1062 eq38933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38952 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq38933
       grind)
    | exact superpose eq38933 eq35
    | exact resolve eq35 eq38933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38933
  have eq38963 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq38951
  have eq38974 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38952
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq38952
    | exact resolve eq38952 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38952
  have eq40276 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq38963
       grind)
    | exact superpose eq38963 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq38963
       grind)
    | exact resolve eq13 eq38963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38963
  have eq40409 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq40276 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40276
  have eq40597 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1168 y X0
       have i₂ := eq40409 y
       grind)
    | exact superpose eq40409 eq1168
    | (have j0 := eq1168 y X0
       grind)
    | exact resolve eq1168 eq40409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40409
  have eq40658 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq40597 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40597
  have eq40681 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40658 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40658
    | (have j0 := eq40658 X0
       grind)
    | exact resolve eq40658 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40658
  have eq41038 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40681 eq38974
    | exact resolve eq38974 eq40681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38974 eq40681
  have eq41049 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq41038
  have eq41082 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq41049
       have r₂ := eq33099
       grind)
    | exact resolve eq41049 eq33099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33099 eq41049
  have eq41102 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41082 eq27
    | exact resolve eq27 eq41082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41103 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41082 eq175
    | exact resolve eq175 eq41082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq41107 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41082 eq1041
    | exact resolve eq1041 eq41082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq41123 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41082 eq1606
    | exact resolve eq1606 eq41082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1606
  have eq41125 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41082 eq1615
    | exact resolve eq1615 eq41082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615
  have eq41160 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq41125
  have eq41162 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq41123
  have eq41181 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq41160
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq41160 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41160
  have eq41192 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq41107
       have r₂ := eq33103
       grind)
    | exact resolve eq41107 eq33103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33103 eq41107
  have eq41589 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq41162 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq41162
       grind)
    | exact resolve eq13 eq41162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41626 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41162 eq1575
    | exact resolve eq1575 eq41162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575 eq41162
  have eq41724 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq41626
  have eq41740 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq41589 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41589
  have eq41802 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41082 eq41724
    | exact resolve eq41724 eq41082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41724
  have eq41803 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq41802
  have eq41964 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41740 eq8100
    | exact resolve eq8100 eq41740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8100 eq41740
  have eq41979 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq41964
  have eq42016 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq41979
       have r₂ := eq41102
       grind)
    | exact resolve eq41979 eq41102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41979
  have eq42032 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41082 eq42016
    | exact resolve eq42016 eq41082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42016
  have eq42033 : x = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq42032
  have eq42434 : (M.op x (M.op x y)) = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq178 x
       have i₂ := eq42033
       grind)
    | exact superpose eq42033 eq178
    | exact resolve eq178 eq42033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq42656 : x = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq42033 eq42434
    | exact resolve eq42434 eq42033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42033 eq42434
  have eq43582 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq42656 eq1475
    | exact resolve eq1475 eq42656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq42656
  have eq43617 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq43582
  have eq43637 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41082 eq43617
    | exact resolve eq43617 eq41082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43617
  have eq43638 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq43637
  have eq43656 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43638 eq31
    | exact resolve eq31 eq43638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44115 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq43656
    | exact resolve eq43656 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43656
  have eq47967 : ∀ X0 : G, (M.op (M.op X0 (σ x)) X0) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41103 eq595
    | exact resolve eq595 eq41103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq41103
  have eq48550 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41803 eq47967
    | exact resolve eq47967 eq41803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48649 : (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47967 eq2338
    | (have j0 := eq2338 (M.op (σ y) (σ x))
       grind)
    | exact resolve eq2338 eq47967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338 eq47967
  have eq48686 : (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq48649
  have eq48766 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq48550
  have eq48810 : (M.op (σ y) (σ x)) = (k (σ y) (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41082 eq48686
    | exact resolve eq48686 eq41082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41082 eq48686
  have eq48873 : (σ y) = (k (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41803 eq48810
    | exact resolve eq48810 eq41803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48810
  have eq48900 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq41803 eq48873
    | exact resolve eq48873 eq41803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41803 eq48873
  have eq48908 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq48900
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq48900 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48900
  have eq49073 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq48766 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq48766
       grind)
    | exact resolve eq13 eq48766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48766
  have eq49221 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq49073 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49073
  have eq49600 : ∀ X0 : G, (σ (σ y)) ≠ (σ (σ y)) ∨ (k X0 (σ (σ y))) = X0 ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq48908 eq1168
    | (have j0 := eq1168 (σ y) X0
       grind)
    | exact resolve eq1168 eq48908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq48908
  have eq49644 : ∀ X0 : G, (k X0 (σ (σ y))) = X0 ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq49600 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49600
  have eq55269 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k x (σ y)) X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq49644 eq43
    | exact resolve eq43 eq49644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq55309 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (k (M.op x y) (σ y)) X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq43638 eq55269
    | exact resolve eq55269 eq43638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43638 eq55269
  have eq55339 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq49221 eq55309
    | exact resolve eq55309 eq49221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55309
  have eq55350 : ∀ X0 : G, (k (σ x) (σ X0)) = (k (σ (M.op x y)) (σ X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq37 eq55339
    | exact resolve eq55339 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq55339
  have eq58235 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41192 eq90
    | exact resolve eq90 eq41192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq41192
  have eq58274 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq58235
    | exact resolve eq58235 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58235
  have eq61598 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58274 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq58274
       grind)
    | exact resolve eq13 eq58274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58274
  have eq61759 : ∀ X0 : G, y = (k x y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq61598 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61598
  have eq65805 : ∀ X0 : G, (σ y) = (k (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq35 y
       have i₂ := eq61759 X0
       grind)
    | exact superpose eq61759 eq35
    | (have j1 := eq61759 X0
       grind)
    | exact resolve eq35 eq61759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq61759
  have eq65843 : ∀ X0 : G, (σ y) = (k (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq65805 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq65805
    | (have j0 := eq65805 X0
       grind)
    | exact resolve eq65805 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65805
  have eq65858 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49221 eq65843
    | (have j0 := eq65843 X0
       have j1 := eq49221 X0
       grind)
    | exact resolve eq65843 eq49221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49221 eq65843
  have eq65865 : ∀ X0 : G, (σ x) = (k (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41181 eq65858
    | exact resolve eq65858 eq41181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41181 eq65858
  have eq65867 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq65865 X0
       have j1 := eq1162 (σ x) X0
       grind)
    | (have r₁ := eq65865 X0
       have r₂ := eq1162 (σ x) x
       grind)
    | (have r₁ := eq65865 (σ x)
       have r₂ := eq1162 (σ x) x
       grind)
    | exact resolve eq65865 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq65865
  have eq65934 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq65867 eq114
    | exact resolve eq114 eq65867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq65867
  have eq65974 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq65934
    | exact resolve eq65934 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65934
  have eq176133 : (σ (M.op x y)) = (k (σ x) (σ (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq55350 eq49644
    | exact resolve eq49644 eq55350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55350
  have eq176152 : (σ (M.op x y)) = (k (σ x) (σ (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq176133
  have eq176211 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq49644 eq176152
    | exact resolve eq176152 eq49644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49644 eq176152
  have eq176273 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq176211
       have r₂ := eq41102
       grind)
    | exact resolve eq176211 eq41102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41102 eq176211
  have eq176325 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq176273 eq31
    | exact resolve eq31 eq176273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176273
  have eq176824 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq176325
    | exact resolve eq176325 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq176325
  have eq176850 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq176824
       grind)
    | exact superpose eq176824 eq18
    | exact resolve eq18 eq176824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176851 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq176824
       grind)
    | exact superpose eq176824 eq24
    | exact resolve eq24 eq176824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176854 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq1038
       have i₂ := eq176824
       grind)
    | exact superpose eq176824 eq1038
    | (have r₁ := eq1038
       have r₂ := eq176824
       grind)
    | exact resolve eq1038 eq176824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038
  have eq176855 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq176824
  have eq176856 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq176854
  have eq176859 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq176851
    | exact resolve eq176851 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176851
  have eq176981 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq176850 eq174
    | exact resolve eq174 eq176850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq176850
  have eq180203 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq176856 eq1673
    | (have j0 := eq1673 x (M.op x y)
       grind)
    | exact resolve eq1673 eq176856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673 eq176856
  have eq180219 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq180203
  have eq180229 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq180219
    | exact resolve eq180219 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180219
  have eq180235 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq180229
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq180229
    | exact resolve eq180229 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180229
  have eq180239 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq180235
    | exact resolve eq180235 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180235
  have eq180242 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq176859 eq180239
    | exact resolve eq180239 eq176859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180239
  have eq180244 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq176859 eq180242
    | exact resolve eq180242 eq176859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180242
  have eq180246 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq26 eq180244
    | exact resolve eq180244 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180244
  have eq180248 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1486 eq180246
    | exact resolve eq180246 eq1486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486 eq180246
  have eq215535 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq180248 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq180248
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq180248
       grind)
    | exact resolve eq13 eq180248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180248
  have eq215789 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq215535 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215535
  have eq218444 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq176981 X0
       have i₂ := eq215789 (M.op X0 X0)
       grind)
    | exact superpose eq215789 eq176981
    | (have j1 := eq215789 X0
       grind)
    | exact resolve eq176981 eq215789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218587 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq218444 X0
       grind)
    | (have r₁ := eq218444 X0
       have r₂ := eq176855
       grind)
    | exact resolve eq218444 eq176855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218444
  have eq218608 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1442 eq218587
    | (have j0 := eq218587 X0
       have j1 := eq1442 X0
       grind)
    | exact resolve eq218587 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442 eq218587
  have eq218613 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq215789 eq218608
    | (have j0 := eq218608 X0
       have j1 := eq215789 X0
       grind)
    | exact resolve eq218608 eq215789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215789 eq218608
  have eq218614 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq218613 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218613
  have eq218728 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq218614 eq107
    | exact resolve eq107 eq218614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq218614
  have eq218768 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq218728
    | exact resolve eq218728 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq218728
  have eq219272 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1126 y y
       have i₂ := eq218768
       grind)
    | exact superpose eq218768 eq1126
    | (have j0 := eq1126 y y
       grind)
    | (have r₁ := eq1126 y y
       have r₂ := eq218768
       grind)
    | exact resolve eq1126 eq218768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq218768
  have eq219292 : y ≠ y ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq219272
  have eq219293 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq219292
  have eq219831 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq219293
       have i₂ := eq44115
       grind)
    | exact superpose eq44115 eq219293
    | exact resolve eq219293 eq44115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44115 eq219293
  have eq220119 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq219831
  have eq220209 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq220119
       have r₂ := eq176855
       grind)
    | exact resolve eq220119 eq176855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220119
  have eq221214 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq220209 eq176981
    | exact resolve eq176981 eq220209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176981
  have eq221260 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq221214
  have eq221340 : x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq220209 eq221260
    | exact resolve eq221260 eq220209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220209 eq221260
  have eq221364 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq221340
       have r₂ := eq176855
       grind)
    | exact resolve eq221340 eq176855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176855 eq221340
  have eq221384 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq221364 eq27
    | exact resolve eq27 eq221364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221364
  have eq221408 : x = y := by
    first
    | (have r₁ := eq221384
       have r₂ := eq176859
       grind)
    | exact resolve eq221384 eq176859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176859 eq221384
  have eq221417 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq221408
       grind)
    | exact superpose eq221408 eq18
    | exact resolve eq18 eq221408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq221418 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq221408
       grind)
    | exact superpose eq221408 eq24
    | exact resolve eq24 eq221408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq221422 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq221408
       grind)
    | exact superpose eq221408 eq1062
    | exact resolve eq1062 eq221408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq221718 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65974
       have i₂ := eq221408
       grind)
    | exact superpose eq221408 eq65974
    | exact resolve eq65974 eq221408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65974 eq221408
  have eq221884 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq221718 eq221422
    | exact resolve eq221422 eq221718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221422 eq221718
  have eq221885 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq221884
  have eq221889 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq221418
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq221418
    | exact resolve eq221418 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221418
  have eq221918 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq221885
       have i₂ := eq221417
       grind)
    | exact superpose eq221417 eq221885
    | exact resolve eq221885 eq221417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221885
  have eq221919 : x = (M.op x y) := by grind
  clear eq221918
  have eq221921 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq221889 eq26
    | exact resolve eq26 eq221889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq221889
  have eq222254 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq221919
       grind)
    | exact superpose eq221919 eq22
    | exact resolve eq22 eq221919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq222512 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq222254 eq20
    | exact resolve eq20 eq222254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222254
  have eq223194 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq221417
       grind)
    | exact superpose eq221417 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq221417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221417
  have eq223399 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq223194 X0
       grind)
    | (have r₁ := eq223194 X0
       have r₂ := eq221919
       grind)
    | exact resolve eq223194 eq221919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223194
  have eq223402 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq223399 X0
       have i₂ := eq221919
       grind)
    | exact superpose eq221919 eq223399
    | exact resolve eq223399 eq221919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221919 eq223399
  have eq223998 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq223402 eq1166
    | (have j0 := eq1166 (M.op x y)
       grind)
    | exact resolve eq1166 eq223402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166 eq223402
  have eq224075 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq223998
  have eq224095 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq224075
    | exact resolve eq224075 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq224075
  have eq224111 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq222512 eq224095
    | exact resolve eq224095 eq222512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224095
  have eq224411 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq224111 eq221921
    | exact resolve eq221921 eq224111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221921 eq224111
  have eq224711 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq224411 eq27
    | exact resolve eq27 eq224411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq224411
  have eq224763 : False := by grind
  exact eq224763

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_x_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq36 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op x y)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (τ (k (k (σ X0) (σ X1)) (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq46 (k X0 X1) X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq46
    | exact resolve eq46 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 X0 (M.op x y)
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op X0 (M.op x y)) (M.op (τ (σ x)) (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq32 eq9
    | (have j0 := eq9 (σ x) X0 (σ y)
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) ≠ X0 ∨ (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) (M.op X1 (M.op X0 X2))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (M.op x y) ≠ (M.op (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq12
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq82
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq82
    | exact resolve eq82 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq86 : (M.op x y) ≠ (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq80
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq80
    | exact resolve eq80 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq87 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) ≠ X0 ∨ (k (M.op X0 X0) (M.op X1 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79 X0 X1 X2
       have i₂ := eq83 (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq83 eq79
    | (have j0 := eq79 X0 X1 X2
       grind)
    | exact resolve eq79 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq89 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) ≠ X0 ∨ (k (k X0 X0) (M.op X1 (M.op X0 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X0 X1 X2
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq87
    | (have j0 := eq87 X0 X1 X2
       grind)
    | exact resolve eq87 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq92 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq56
    | exact resolve eq56 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq123 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq14
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq143 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq143
       have i₂ := eq83 sF5
       grind)
    | exact superpose eq83 eq143
    | exact resolve eq143 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq164 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ x)) (τ (σ x))) := by
    first
    | (have i₁ := eq141
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq141
    | exact resolve eq141 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq175 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq162
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq162
    | exact resolve eq162 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq177 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq164
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq164
    | exact resolve eq164 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq188 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq175
       have r₂ := eq84
       grind)
    | exact resolve eq175 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq190 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have r₁ := eq177
       have r₂ := eq86
       grind)
    | exact resolve eq177 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq255 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq255
    | exact resolve eq255 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq331 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq66
    | exact resolve eq66 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq332 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 X0 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq333 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1) X1
       have i₂ := eq83 (M.op X0 X1)
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : (τ (σ x)) = (M.op (k (M.op x y) (M.op x y)) (M.op (τ (σ x)) (τ (σ x)))) := by
    first
    | (have i₁ := eq63 sF2
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq63
    | exact resolve eq63 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq339 : (τ (σ x)) = (M.op (k (M.op x y) (M.op x y)) (k (τ (σ x)) (τ (σ x)))) := by
    first
    | (have i₁ := eq337
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq337
    | exact resolve eq337 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq340 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq336
    | exact resolve eq336 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq341 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X0) ∨ (M.op X1 X0) = (k X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0 X1
       have i₂ := eq83 X1
       grind)
    | exact superpose eq83 eq332
    | (have j0 := eq332 X0 X1
       grind)
    | (have r₁ := eq332 X0 X0
       have r₂ := eq83 X0
       grind)
    | exact resolve eq332 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq368 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq65 sF6
       have i₂ := eq83 sF6
       grind)
    | exact superpose eq83 eq65
    | exact resolve eq65 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq381 : (σ x) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq368
       have i₂ := eq83 sF4
       grind)
    | exact superpose eq83 eq368
    | exact resolve eq368 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq431 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq190 eq15
    | exact resolve eq15 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq432 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq431
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq431
    | exact resolve eq431 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq433 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq432
    | exact resolve eq432 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432
  have eq435 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq433 eq15
    | exact resolve eq15 eq433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq436 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq435
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq435
    | exact resolve eq435 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq437 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq436
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq436
    | exact resolve eq436 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq438 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq437
    | exact resolve eq437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq439 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq188 eq84
    | exact resolve eq84 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq441 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq188 eq33
    | exact resolve eq33 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  have eq444 : (k (σ x) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq439
       have r₂ := eq442
       grind)
    | exact resolve eq439 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq442
  have eq445 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq438 eq36
    | exact resolve eq36 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq453 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq438 eq441
    | (have r₁ := eq441
       have r₂ := eq438
       grind)
    | exact resolve eq441 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq454 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq438
  have eq455 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq453
  have eq463 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq445
       have i₂ := eq123 sF5 sF5
       grind)
    | exact superpose eq123 eq445
    | exact resolve eq445 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445
  have eq509 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (M.op X0 X0) (M.op x (M.op X0 x)) X1 X2
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq32 eq62
    | (have j0 := eq62 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq62 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq62
    | exact resolve eq62 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 (M.op X0 x) x
       have i₂ := eq83 (M.op X0 x)
       grind)
    | exact superpose eq83 eq62
    | exact resolve eq62 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq62 X1 X4 X0 X2
       grind)
    | exact superpose eq62 eq9
    | exact resolve eq9 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq548 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (k (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq540 X0 X1 X2 X3 X4
       have i₂ := eq83 (M.op X4 X1)
       grind)
    | exact superpose eq83 eq540
    | exact resolve eq540 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540
  have eq554 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq531 X0 X1 X2
       have i₂ := eq83 (k (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq83 eq531
    | exact resolve eq531 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq567 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (k (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq518 X0 X1 X2
       have i₂ := eq83 (M.op X1 X0)
       grind)
    | exact superpose eq83 eq518
    | exact resolve eq518 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq569 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (k (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq516 X0 X1
       have i₂ := eq83 (M.op X0 (M.op sF5 X1))
       grind)
    | exact superpose eq83 eq516
    | exact resolve eq516 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq576 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (k (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq509 X0 X1 X2
       have i₂ := eq83 (M.op X1 (M.op (M.op X0 X0) X2))
       grind)
    | exact superpose eq83 eq509
    | exact resolve eq509 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq591 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (k X0 X0) X2)) = (M.op X0 (k (M.op X1 (M.op (k X0 X0) X2)) (M.op X1 (M.op (k X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq576 X0 X1 X2
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq576
    | exact resolve eq576 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq782 : ∀ X0 X1 : G, (k (M.op X1 X0) (M.op X1 X0)) ≠ X0 ∨ (k (k X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1 (M.op X0 X0)
       have i₂ := eq66 X0
       grind)
    | exact superpose eq66 eq89
    | exact resolve eq89 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq89
  have eq1414 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq256 X0 X0
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq256
    | exact resolve eq256 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1430 : (τ (σ y)) = (M.op (M.op x y) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | exact superpose eq42 eq256
    | exact resolve eq256 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1471 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1414 X0
       have i₂ := eq83 (k X0 X0)
       grind)
    | exact superpose eq83 eq1414
    | exact resolve eq1414 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1476 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq463 eq1430
    | exact resolve eq1430 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq1480 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (τ (σ y))) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1430 eq9
    | exact resolve eq9 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1496 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (τ (σ y))) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1480 X0
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq1480
    | exact resolve eq1480 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480
  have eq1499 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1476
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq1476
    | exact resolve eq1476 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1501 : (M.op x y) = (M.op (k (τ (σ y)) (τ (σ y))) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1496 (τ sF5)
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq1496
    | exact resolve eq1496 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq1562 : ∀ X0 : G, (k (τ (σ y)) (τ (σ y))) = (M.op (M.op X0 (M.op x y)) (M.op (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    intro X0
    first
    | exact superpose eq1501 eq9
    | exact resolve eq9 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1580 : ∀ X0 : G, (k (τ (σ y)) (τ (σ y))) = (M.op (M.op X0 (M.op x y)) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq1562 X0
       have i₂ := eq83 (k (τ sF5) (τ sF5))
       grind)
    | exact superpose eq83 eq1562
    | exact resolve eq1562 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1562
  have eq1584 : ∀ X0 : G, (k (τ (σ y)) (τ (σ y))) = (M.op (M.op X0 (M.op x y)) (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq1580 X0
       have i₂ := eq1471 (τ sF5)
       grind)
    | exact superpose eq1471 eq1580
    | exact resolve eq1580 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1580
  have eq1601 : (σ y) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1499 eq35
    | exact resolve eq35 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1607 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1601
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1601
    | exact resolve eq1601 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601
  have eq1610 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq1607
    | exact resolve eq1607 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq1659 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq1610 eq256
    | exact resolve eq256 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1665 : (σ (σ y)) = (k (σ (σ (M.op x y))) (σ (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1610 eq15
    | exact resolve eq15 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610
  have eq1785 : (k (τ (σ y)) (τ (σ y))) = (M.op (k (M.op x y) (M.op x y)) (τ (σ y))) := by
    first
    | (have i₁ := eq1584 sF2
       have i₂ := eq83 sF2
       grind)
    | exact superpose eq83 eq1584
    | exact resolve eq1584 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1584
  have eq1898 : (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1659 sF3
       have i₂ := eq83 sF3
       grind)
    | exact superpose eq83 eq1659
    | exact resolve eq1659 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1659
  have eq2129 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq340 (k (M.op X0 X1) (M.op X0 X1)) (k X0 X0)
       have i₂ := eq340 X0 X1
       grind)
    | exact superpose eq340 eq340
    | exact resolve eq340 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2133 : (k (M.op x y) (M.op x y)) = (M.op (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq1785 eq340
    | exact resolve eq340 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2152 : ∀ X0 X1 : G, (M.op (k X0 X0) (k X0 X0)) ≠ X0 ∨ (M.op (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (k X0 X0) = (k (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq340 X0 X1
       grind)
    | exact superpose eq340 eq13
    | (have j0 := eq13 (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact resolve eq13 eq340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2169 : ∀ X0 X1 : G, (k (k X0 X0) (k X0 X0)) ≠ X0 ∨ (M.op (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (k X0 X0) = (k (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2152 X0 X1
       have i₂ := eq83 (k X0 X0)
       grind)
    | exact superpose eq83 eq2152
    | (have j0 := eq2152 X0 X1
       grind)
    | exact resolve eq2152 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2152
  have eq2173 : (k (M.op x y) (M.op x y)) = (M.op (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (M.op x y)) := by
    first
    | (have i₁ := eq2133
       have i₂ := eq1471 sF2
       grind)
    | exact superpose eq1471 eq2133
    | exact resolve eq2133 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2133
  have eq2176 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (k X0 X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2129 X0 X1
       have i₂ := eq1471 (M.op X0 X1)
       grind)
    | exact superpose eq1471 eq2129
    | exact resolve eq2129 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2129
  have eq2186 : ∀ X0 X1 : G, (M.op (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (k X0 X0) = (k (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq2169 X0 X1
       grind)
    | (have r₁ := eq2169 X0 X1
       have r₂ := eq1471 X0
       grind)
    | exact resolve eq2169 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169
  have eq2188 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq2173
       have i₂ := eq1471 (τ sF5)
       grind)
    | exact superpose eq1471 eq2173
    | exact resolve eq2173 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173
  have eq2190 : ∀ X0 X1 : G, (k (k (M.op X0 X1) (M.op X0 X1)) (k (M.op X0 X1) (M.op X0 X1))) = X0 ∨ (k X0 X0) = (k (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2186 X0 X1
       have i₂ := eq83 (k (M.op X0 X1) (M.op X0 X1))
       grind)
    | exact superpose eq83 eq2186
    | (have j0 := eq2186 X0 X1
       grind)
    | exact resolve eq2186 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186
  have eq2191 : ∀ X0 X1 : G, (k X0 X0) = (k (k X0 X0) (k (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2190 X0 X1
       have i₂ := eq1471 (M.op X0 X1)
       grind)
    | exact superpose eq1471 eq2190
    | (have j0 := eq2190 X0 X1
       grind)
    | exact resolve eq2190 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190
  have eq2201 : (k (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq2188 eq13
    | (have j0 := eq13 (M.op x y) (τ (σ y))
       grind)
    | exact resolve eq13 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2218 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have r₁ := eq2201
       have r₂ := eq83 (M.op x y)
       grind)
    | exact resolve eq2201 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq2222 : (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq2218
       have i₂ := eq83 (τ sF5)
       grind)
    | exact superpose eq83 eq2218
    | exact resolve eq2218 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2218
  have eq2275 : (k (M.op x y) (M.op x y)) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq2188 eq333
    | exact resolve eq333 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188
  have eq2282 : (σ (M.op x y)) ≠ (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1898 eq333
    | exact resolve eq333 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq333 eq1898
  have eq2290 : (σ (M.op x y)) = (k (σ y) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq2282
       have r₂ := eq1471 (σ (M.op x y))
       grind)
    | exact resolve eq2282 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282
  have eq2500 : ∀ X0 : G, (k (τ (σ y)) (τ (σ y))) = (M.op (M.op X0 (τ (σ y))) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) := by
    intro X0
    first
    | exact superpose eq1785 eq567
    | exact resolve eq567 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq2536 : ∀ X0 : G, (k (τ (σ y)) (τ (σ y))) = (M.op (M.op X0 (τ (σ y))) (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2500 X0
       have i₂ := eq1471 (τ sF5)
       grind)
    | exact superpose eq1471 eq2500
    | exact resolve eq2500 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2500
  have eq2975 : (k (τ (σ y)) (τ (σ y))) = (M.op (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq42 eq2536
    | exact resolve eq2536 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2976 : (k (τ (σ y)) (τ (σ y))) = (M.op (k (τ (σ y)) (τ (σ y))) (τ (σ y))) := by
    first
    | exact superpose eq1785 eq2536
    | exact resolve eq2536 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785 eq2536
  have eq3053 : (M.op x y) = (M.op (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq2975 eq340
    | exact resolve eq340 eq2975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3057 : (M.op x y) = (M.op (τ (σ y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq3053
       have i₂ := eq1471 (τ sF5)
       grind)
    | exact superpose eq1471 eq3053
    | exact resolve eq3053 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3053
  have eq3083 : (τ (σ y)) = (M.op (k (M.op x y) (M.op x y)) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | exact superpose eq3057 eq340
    | exact resolve eq340 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3057
  have eq3207 : (k (M.op x y) (M.op x y)) = (M.op (k (τ (σ y)) (τ (σ y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq3083 eq340
    | exact resolve eq340 eq3083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3083
  have eq3211 : (k (M.op x y) (M.op x y)) = (M.op (k (τ (σ y)) (τ (σ y))) (M.op x y)) := by
    first
    | (have i₁ := eq3207
       have i₂ := eq1471 sF2
       grind)
    | exact superpose eq1471 eq3207
    | exact resolve eq3207 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3207
  have eq3421 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq341 (k X0 X0) X0
       have i₂ := eq331 X0
       grind)
    | exact superpose eq331 eq341
    | (have j0 := eq341 X0 X0
       grind)
    | exact resolve eq341 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3450 : (M.op x y) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq341
    | (have j0 := eq341 (τ (σ y)) (τ (σ x))
       grind)
    | exact resolve eq341 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3468 : (k (τ (σ y)) (τ (σ y))) ≠ (k (τ (σ y)) (τ (σ y))) ∨ (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq2975 eq341
    | (have j0 := eq341 (τ (σ y)) (M.op x y)
       grind)
    | (have r₁ := eq341 (τ (σ y)) (M.op x y)
       have r₂ := eq2975
       grind)
    | exact resolve eq341 eq2975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975
  have eq3470 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq341
    | (have j0 := eq341 (σ y) (σ x)
       grind)
    | exact resolve eq341 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq3474 : (k (M.op x y) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by grind
  clear eq3468
  have eq3502 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3421 X0
       grind)
    | (have r₁ := eq3421 X0
       have r₂ := eq1471 X0
       grind)
    | exact resolve eq3421 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3421
  have eq3529 : ∀ X0 : G, (k (k (σ (M.op x y)) (σ (M.op x y))) X0) = (τ (k (σ (σ y)) (σ X0))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq1665 eq48
    | exact resolve eq48 eq1665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq3570 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ (M.op x y)) (σ (M.op x y))) X0) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3529 x
       have i₂ := eq46 sF5 x
       grind)
    | exact superpose eq46 eq3529
    | exact resolve eq3529 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3529
  have eq3686 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 (M.op (τ (σ y)) X2))) (k (M.op x y) (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq42 eq548
    | exact resolve eq548 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3699 : ∀ X0 X1 X2 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op (M.op x y) X2))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3211 eq548
    | exact resolve eq548 eq3211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3211
  have eq3706 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (M.op (σ y) X2))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq32 eq548
    | (have j0 := eq548 X1 (σ y) X2 X0 (σ x)
       grind)
    | exact resolve eq548 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq3745 : ∀ X0 X1 X2 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op X1 (M.op (M.op x y) X2))) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3699 X0 X1 X2
       have i₂ := eq1471 sF2
       grind)
    | exact superpose eq1471 eq3699
    | exact resolve eq3699 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3699
  have eq3817 : ∀ X0 : G, (k (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (k (k (M.op (σ y) X0) (M.op (σ y) X0)) (k (M.op (σ y) X0) (M.op (σ y) X0)))) := by
    intro X0
    first
    | (have i₁ := eq569 (M.op sF5 x) x
       have i₂ := eq83 (M.op sF5 x)
       grind)
    | exact superpose eq83 eq569
    | exact resolve eq569 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq3852 : ∀ X0 : G, (k (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq3817 X0
       have i₂ := eq1471 (M.op sF5 X0)
       grind)
    | exact superpose eq1471 eq3817
    | exact resolve eq3817 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817
  have eq4511 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq3745 (M.op x (M.op (M.op sF2 x) x)) (M.op sF2 x) x
       have i₂ := eq9 (M.op sF2 x) x x
       grind)
    | exact superpose eq9 eq3745
    | exact resolve eq3745 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3745
  have eq5923 : ∀ X0 : G, (M.op x y) = (M.op (M.op (τ (σ y)) X0) (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq3686 (M.op x (M.op (M.op (τ sF5) x) x)) (M.op (τ sF5) x) x
       have i₂ := eq9 (M.op (τ sF5) x) x x
       grind)
    | exact superpose eq9 eq3686
    | exact resolve eq3686 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3686
  have eq6707 : ∀ X0 X1 : G, (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) = (M.op X0 (k (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 (M.op (k X0 X0) x) x
       have i₂ := eq83 (M.op (k X0 X0) x)
       grind)
    | exact superpose eq83 eq591
    | exact resolve eq591 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6746 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op (k (M.op x y) (M.op x y)) X1)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq4511 (k (M.op X1 (M.op (k sF2 sF2) x)) (M.op X1 (M.op (k sF2 sF2) x)))
       have i₂ := eq591 sF2 X1 x
       grind)
    | exact superpose eq591 eq4511
    | exact resolve eq4511 eq591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq4511
  have eq6764 : ∀ X0 X1 : G, (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) = (M.op X0 (M.op (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6707 X0 X1
       have i₂ := eq1471 (M.op (k X0 X0) X1)
       grind)
    | exact superpose eq1471 eq6707
    | exact resolve eq6707 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6707
  have eq6775 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X0 (τ (σ x))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq339 eq6746
    | exact resolve eq6746 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6746
  have eq6861 : (k (M.op x y) (M.op x y)) = (M.op (k (τ (σ x)) (τ (σ x))) (M.op x y)) := by
    first
    | (have i₁ := eq6775 (τ sF4)
       have i₂ := eq83 (τ sF4)
       grind)
    | exact superpose eq83 eq6775
    | exact resolve eq6775 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6775
  have eq7008 : (k (τ (σ x)) (τ (σ x))) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x))))) := by
    first
    | exact superpose eq6861 eq340
    | exact resolve eq340 eq6861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6861
  have eq7026 : (k (τ (σ x)) (τ (σ x))) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) := by
    first
    | (have i₁ := eq7008
       have i₂ := eq1471 (τ sF4)
       grind)
    | exact superpose eq1471 eq7008
    | exact resolve eq7008 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7008
  have eq7044 : (k (τ (σ x)) (τ (σ x))) = (M.op (M.op x y) (τ (σ x))) := by
    first
    | (have i₁ := eq7026
       have i₂ := eq1471 sF2
       grind)
    | exact superpose eq1471 eq7026
    | exact resolve eq7026 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7026
  have eq7278 : ∀ X0 : G, (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)) = (M.op (M.op x y) (k (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)) (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)))) := by
    intro X0
    first
    | exact superpose eq42 eq554
    | exact resolve eq554 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7329 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X2 (M.op X1 X0)) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq554 (M.op X1 X0) (k X0 X0) X2
       have i₂ := eq256 X0 X1
       grind)
    | exact superpose eq256 eq554
    | exact resolve eq554 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7372 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X1 (M.op (τ (σ y)) X0)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq5923 eq554
    | exact resolve eq554 eq5923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5923
  have eq7494 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op X1 (M.op (τ (σ y)) X0)) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq7372 X0 X1
       have i₂ := eq1471 sF2
       grind)
    | exact superpose eq1471 eq7372
    | exact resolve eq7372 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7372
  have eq7537 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op X2 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7329 X0 X1 X2
       have i₂ := eq1471 X0
       grind)
    | exact superpose eq1471 eq7329
    | exact resolve eq7329 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7329
  have eq7587 : ∀ X0 : G, (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq7278 X0
       have i₂ := eq1471 (M.op (τ sF5) X0)
       grind)
    | exact superpose eq1471 eq7278
    | exact resolve eq7278 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7278
  have eq7708 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7494 X0 (M.op (τ sF5) X0)
       have i₂ := eq83 (M.op (τ sF5) X0)
       grind)
    | exact superpose eq83 eq7494
    | exact resolve eq7494 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq7494
  have eq33408 : ∀ X0 X1 : G, (τ (σ y)) = (M.op (M.op X0 (M.op (τ (σ y)) X1)) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq2222 eq334
    | exact resolve eq334 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33435 : (σ (k (M.op x y) (M.op x y))) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq2222 eq15
    | exact resolve eq15 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33488 : (σ (k (M.op x y) (M.op x y))) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq33435
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq33435
    | exact resolve eq33435 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33435
  have eq33525 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq33488
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq33488
    | exact resolve eq33488 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33488
  have eq33531 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq26 eq33525
    | exact resolve eq33525 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33525
  have eq35578 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (k (σ y) (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq33531 eq331
    | exact resolve eq331 eq33531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35607 : (σ (k (σ y) (σ y))) = (k (σ (σ (M.op x y))) (σ (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq33531 eq15
    | exact resolve eq15 eq33531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35663 : (k (σ (σ y)) (σ (σ y))) = (k (σ (σ (M.op x y))) (σ (σ (M.op x y)))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq35607
       have i₂ := eq15 sF5 sF5
       grind)
    | exact superpose eq15 eq35607
    | exact resolve eq35607 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35607
  have eq37826 : (k (σ (M.op x y)) (σ (M.op x y))) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ y)) = (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq35578 eq782
    | exact resolve eq782 eq35578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782 eq35578
  have eq37883 : (k (σ y) (σ y)) = (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (σ (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have r₁ := eq37826
       have r₂ := eq33531
       grind)
    | exact resolve eq37826 eq33531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33531 eq37826
  have eq37905 : (k (σ y) (σ (M.op x y))) = (k (σ y) (σ y)) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq37883
       have i₂ := eq1471 sF5
       grind)
    | exact superpose eq1471 eq37883
    | exact resolve eq37883 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37883
  have eq37917 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq190 eq3450
    | (have r₁ := eq3450
       have r₂ := eq190
       grind)
    | exact resolve eq3450 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq3450
  have eq37918 : (M.op x y) = (k (τ (σ x)) (τ (σ x))) ∨ (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by grind
  clear eq37917
  have eq37920 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have r₁ := eq37918
       have r₂ := eq86
       grind)
    | exact resolve eq37918 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq37918
  have eq38315 : (k (τ (σ y)) (M.op x y)) = (τ (k (σ y) (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq37905 eq92
    | exact resolve eq92 eq37905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq37905
  have eq38340 : (k (τ (σ y)) (M.op x y)) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq38315
       have i₂ := eq123 sF5 sF5
       grind)
    | exact superpose eq123 eq38315
    | exact resolve eq38315 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38315
  have eq41294 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq37920 eq15
    | exact resolve eq15 eq37920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37920
  have eq41328 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq41294
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq41294
    | exact resolve eq41294 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41294
  have eq41333 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq41328
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq41328
    | exact resolve eq41328 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41328
  have eq42094 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq41333 eq15
    | exact resolve eq15 eq41333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41333
  have eq42115 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq42094
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq42094
    | exact resolve eq42094 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42094
  have eq42117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq42115
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq42115
    | exact resolve eq42115 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42115
  have eq42118 : (σ y) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq42117
    | exact resolve eq42117 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42117
  have eq42127 : (τ (σ y)) = (k (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42118 eq123
    | exact resolve eq123 eq42118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42373 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1499 eq42127
    | exact resolve eq42127 eq1499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499 eq42127
  have eq42405 : (k (M.op x y) (M.op x y)) = (k (k (M.op x y) (M.op x y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq42373
  have eq42887 : ∀ X0 : G, (k X0 X0) = (M.op (k (M.op (τ (σ y)) X0) (M.op (τ (σ y)) X0)) X0) := by
    intro X0
    first
    | exact superpose eq7587 eq7537
    | exact resolve eq7537 eq7587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7537 eq7587
  have eq44438 : (σ (k (M.op x y) (M.op x y))) = (k (σ (k (M.op x y) (M.op x y))) (σ (τ (σ x)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq42405 eq15
    | exact resolve eq15 eq42405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42405
  have eq44472 : (σ (k (M.op x y) (M.op x y))) = (k (σ (k (M.op x y) (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq44438
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq44438
    | exact resolve eq44438 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44438
  have eq44480 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq44472
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq44472
    | exact resolve eq44472 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44472
  have eq44482 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq44480
    | exact resolve eq44480 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44480
  have eq44493 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq44482 eq3570
    | exact resolve eq3570 eq44482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3570 eq44482
  have eq44513 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq44493
  have eq44560 : (σ (M.op x y)) = (k (σ y) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq44513 eq2290
    | exact resolve eq2290 eq44513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq44625 : (σ (M.op x y)) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq44513 eq1471
    | exact resolve eq1471 eq44513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44513
  have eq44685 : (σ (M.op x y)) = (k (σ y) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq44560
  have eq45869 : (k (σ y) (σ x)) ≠ (k (σ y) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq44685
  have eq46147 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X1 (k (M.op (σ y) X0) (M.op (σ y) X0))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq42887 eq3706
    | exact resolve eq3706 eq42887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3706 eq42887
  have eq50380 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k (τ (k (σ X0) (σ X0))) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (k (σ X0) (σ X0)) X0
       have i₂ := eq3502 (σ X0)
       grind)
    | exact superpose eq3502 eq47
    | (have j1 := eq3502 (σ X0)
       grind)
    | exact resolve eq47 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3502
  have eq50402 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50380 x
       have i₂ := eq46 x x
       grind)
    | exact superpose eq46 eq50380
    | (have j0 := eq50380 X0
       grind)
    | exact resolve eq50380 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50380
  have eq51507 : (k (σ y) (σ x)) ≠ (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq44625
  have eq53118 : (k (σ y) (σ y)) ≠ (k (σ y) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq188 eq3470
    | (have r₁ := eq3470
       have r₂ := eq188
       grind)
    | exact resolve eq3470 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq3470
  have eq53119 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq53118
  have eq53120 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq53119
       have r₂ := eq444
       grind)
    | exact resolve eq53119 eq444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq53119
  have eq73177 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (k (k (M.op (k (τ (σ y)) (τ (σ y))) X0) (M.op (k (τ (σ y)) (τ (σ y))) X0)) (k (M.op (k (τ (σ y)) (τ (σ y))) X0) (M.op (k (τ (σ y)) (τ (σ y))) X0))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7708 (M.op (k (τ sF5) (τ sF5)) x)
       have i₂ := eq6764 (τ sF5) x
       grind)
    | exact superpose eq6764 eq7708
    | exact resolve eq7708 eq6764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7708
  have eq73221 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (k (τ (σ y)) (τ (σ y))) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq73177 X0
       have i₂ := eq1471 (M.op (k (τ sF5) (τ sF5)) X0)
       grind)
    | exact superpose eq1471 eq73177
    | exact resolve eq73177 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73177
  have eq73357 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (k (M.op x y) (M.op x y)) X0) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq2222 eq73221
    | exact resolve eq73221 eq2222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222 eq73221
  have eq74167 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (k (σ y) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq46147 (k sF5 sF5) x
       have i₂ := eq331 sF5
       grind)
    | exact superpose eq331 eq46147
    | exact resolve eq46147 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331 eq46147
  have eq74566 : ∀ X0 X1 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X1 (M.op X0 (k (σ y) (σ y)))) (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq74167 eq554
    | exact resolve eq554 eq74167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq74167
  have eq74673 : ∀ X0 X1 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X1 (M.op X0 (k (σ y) (σ y)))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq74566 X0 X1
       have i₂ := eq1471 sF6
       grind)
    | exact superpose eq1471 eq74566
    | exact resolve eq74566 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74566
  have eq75275 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (k (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq74673 (k sF5 sF5) (M.op x (M.op (k sF5 sF5) x))
       have i₂ := eq9 (k sF5 sF5) x x
       grind)
    | exact superpose eq9 eq74673
    | exact resolve eq74673 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74673
  have eq76776 : (k (k (σ y) (σ y)) (k (σ y) (σ y))) = (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq75275 eq2191
    | exact resolve eq2191 eq75275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2191 eq75275
  have eq76905 : (k (k (σ y) (σ y)) (k (σ y) (σ y))) = (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (M.op (σ x) (σ y))) ∨ (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq76776
       have i₂ := eq1471 sF6
       grind)
    | exact superpose eq1471 eq76776
    | exact resolve eq76776 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76776
  have eq77039 : (k (σ y) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq76905
       have i₂ := eq1471 sF5
       grind)
    | exact superpose eq1471 eq76905
    | exact resolve eq76905 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76905
  have eq78313 : (σ x) = (M.op (k (σ y) (σ y)) (k (σ x) (σ x))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq77039 eq381
    | exact resolve eq381 eq77039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq85574 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq78313 eq6764
    | exact resolve eq6764 eq78313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78313
  have eq85793 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq85574 eq3852
    | exact resolve eq3852 eq85574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3852 eq85574
  have eq85970 : (σ x) = (M.op (M.op (σ x) (σ y)) (k (σ x) (σ x))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq85793
       have i₂ := eq1471 sF4
       grind)
    | exact superpose eq1471 eq85793
    | exact resolve eq85793 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85793
  have eq86700 : (k (σ x) (σ x)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ x)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq85970 eq2176
    | exact resolve eq2176 eq85970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2176 eq85970
  have eq91524 : (k (σ x) (σ x)) = (M.op (k (σ y) (σ y)) (σ x)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq77039 eq86700
    | exact resolve eq86700 eq77039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77039 eq86700
  have eq91654 : (k (σ x) (σ x)) = (M.op (k (σ y) (σ y)) (σ x)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq91524
  have eq93614 : (k (σ y) (σ y)) = (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq91654 eq340
    | exact resolve eq340 eq91654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340 eq91654
  have eq93754 : (k (σ y) (σ y)) = (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq93614
       have i₂ := eq1471 sF5
       grind)
    | exact superpose eq1471 eq93614
    | exact resolve eq93614 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93614
  have eq93792 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq93754
       have i₂ := eq1471 sF4
       grind)
    | exact superpose eq1471 eq93754
    | exact resolve eq93754 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93754
  have eq93803 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq32 eq93792
    | exact resolve eq93792 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq93792
  have eq93810 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ y) = (k (σ y) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq455 eq93803
    | exact resolve eq93803 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq93803
  have eq94006 : (σ y) = (k (σ y) (k (σ y) (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq93810
       have r₂ := eq454
       grind)
    | exact resolve eq93810 eq454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq93810
  have eq94290 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq94006 eq45869
    | exact resolve eq45869 eq94006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45869 eq94006
  have eq94312 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq94290
  have eq94317 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq94312
       have r₂ := eq42118
       grind)
    | exact resolve eq94312 eq42118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42118 eq94312
  have eq94687 : (M.op x y) = (τ (k (σ y) (σ x))) := by
    first
    | exact superpose eq94317 eq36
    | exact resolve eq36 eq94317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq94731 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq94687
       have i₂ := eq123 sF4 sF5
       grind)
    | exact superpose eq123 eq94687
    | exact resolve eq94687 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94687
  have eq266349 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op X0 (τ (σ y))) (k (τ (σ y)) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq38340 eq256
    | exact resolve eq256 eq38340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq38340
  have eq366216 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (σ (k X0 X0)) = (k (σ (k X0 X0)) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq50402 (k X0 X0)
       have i₂ := eq1471 X0
       grind)
    | exact superpose eq1471 eq50402
    | (have j0 := eq50402 (k X0 X0)
       grind)
    | exact resolve eq50402 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50402
  have eq366319 : ∀ X0 : G, (k (σ X0) (σ X0)) = (k (k (σ X0) (σ X0)) (k (σ X0) (σ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq366216 x
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq366216
    | (have j0 := eq366216 X0
       grind)
    | exact resolve eq366216 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366216
  have eq366342 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq366319 X0
       have i₂ := eq1471 (σ X0)
       grind)
    | exact superpose eq1471 eq366319
    | (have j0 := eq366319 X0
       grind)
    | exact resolve eq366319 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366319
  have eq366376 : ∀ X0 X1 : G, (τ (k (σ X0) (σ X1))) = (k (k X0 X0) X1) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X0 X1
       have i₂ := eq366342 X0
       grind)
    | exact superpose eq366342 eq48
    | (have j1 := eq366342 X0
       grind)
    | exact resolve eq48 eq366342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366342
  have eq366521 : ∀ X0 X1 : G, (k X0 X1) = (k (k X0 X0) X1) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq366376 X0 X1
       have i₂ := eq46 X0 X1
       grind)
    | exact superpose eq46 eq366376
    | (have j0 := eq366376 X0 X1
       grind)
    | exact resolve eq366376 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366376
  have eq369241 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1471 X0
       have i₂ := eq366521 X0 (k X0 X0)
       grind)
    | exact superpose eq366521 eq1471
    | (have j1 := eq366521 X0 x
       grind)
    | exact resolve eq1471 eq366521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366521
  have eq369394 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq369241 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369241
  have eq371319 : (τ (σ y)) = (k (τ (σ y)) (k (M.op x y) (M.op x y))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq3474 eq369394
    | exact resolve eq369394 eq3474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371328 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq369394 (k X0 X0)
       have i₂ := eq1471 X0
       grind)
    | exact superpose eq1471 eq369394
    | exact resolve eq369394 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369394
  have eq375518 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (k (M.op x y) (M.op x y)))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq371319 eq15
    | exact resolve eq15 eq371319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371319
  have eq375523 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq375518
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq375518
    | exact resolve eq375518 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375518
  have eq375524 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq26 eq375523
    | exact resolve eq375523 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375523
  have eq375525 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (k (k (σ y) (σ x)) (k (σ y) (σ x)))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq94317 eq375524
    | exact resolve eq375524 eq94317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375524
  have eq375526 : (σ y) = (k (σ y) (k (k (σ y) (σ x)) (k (σ y) (σ x)))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq375525
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq375525
    | exact resolve eq375525 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375525
  have eq391872 : (k (M.op x y) (M.op x y)) ≠ (k (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq3474 eq2275
    | (have r₁ := eq2275
       have r₂ := eq3474
       grind)
    | exact resolve eq2275 eq3474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275 eq3474
  have eq391879 : (k (M.op x y) (M.op x y)) = (k (M.op x y) (τ (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by grind
  clear eq391872
  have eq392028 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (τ (σ y)))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq391879 eq15
    | exact resolve eq15 eq391879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391879
  have eq392038 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ y)) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq392028
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq392028
    | exact resolve eq392028 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392028
  have eq392047 : (k (σ (M.op x y)) (σ y)) = (σ (k (M.op x y) (M.op x y))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq26 eq392038
    | exact resolve eq392038 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392038
  have eq392050 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq392047
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq392047
    | exact resolve eq392047 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392047
  have eq392052 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq26 eq392050
    | exact resolve eq392050 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392050
  have eq392053 : (k (k (σ y) (σ x)) (k (σ y) (σ x))) = (k (k (σ y) (σ x)) (σ y)) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq94317 eq392052
    | exact resolve eq392052 eq94317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392052
  have eq408136 : (k (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq339 eq73357
    | exact resolve eq73357 eq339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339 eq73357
  have eq408401 : ∀ X0 : G, (τ (σ x)) = (M.op (M.op X0 (k (M.op x y) (M.op x y))) (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq408136 eq334
    | exact resolve eq334 eq408136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq408136
  have eq414834 : (σ (σ (M.op x y))) = (k (k (σ (σ y)) (σ (σ y))) (k (σ (σ y)) (σ (σ y)))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq35663 eq1471
    | exact resolve eq1471 eq35663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35663
  have eq414879 : (σ (σ (M.op x y))) = (σ (σ y)) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq414834
       have i₂ := eq1471 (σ sF5)
       grind)
    | exact superpose eq1471 eq414834
    | exact resolve eq414834 eq1471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471 eq414834
  have eq414920 : (σ (σ y)) = (σ (k (σ y) (σ x))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq94317 eq414879
    | exact resolve eq414879 eq94317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414879
  have eq414945 : (σ (σ y)) = (k (σ (σ y)) (σ (σ x))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | (have i₁ := eq414920
       have i₂ := eq15 sF5 sF4
       grind)
    | exact superpose eq15 eq414920
    | exact resolve eq414920 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414920
  have eq415145 : ∀ X0 : G, (k (k (σ y) (σ x)) X0) = (τ (k (σ (σ y)) (σ X0))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq414945 eq48
    | exact resolve eq48 eq414945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq414945
  have eq415159 : ∀ X0 : G, (k (σ y) X0) = (k (k (σ y) (σ x)) X0) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq415145 x
       have i₂ := eq46 sF5 x
       grind)
    | exact superpose eq46 eq415145
    | exact resolve eq415145 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq415145
  have eq416124 : ∀ X0 : G, (τ (k (σ y) (σ X0))) = (k (τ (k (σ y) (σ x))) X0) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq415159 eq47
    | exact resolve eq47 eq415159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415159
  have eq416170 : ∀ X0 : G, (τ (k (σ y) (σ X0))) = (k (k (τ (σ y)) (τ (σ x))) X0) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq416124 X0
       have i₂ := eq123 sF4 sF5
       grind)
    | exact superpose eq123 eq416124
    | exact resolve eq416124 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416124
  have eq416192 : ∀ X0 : G, (τ (k (σ y) (σ X0))) = (k (M.op x y) X0) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq94731 eq416170
    | exact resolve eq416170 eq94731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416170
  have eq416201 : ∀ X0 : G, (k (M.op x y) X0) = (k (τ (σ y)) X0) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | (have i₁ := eq416192 x
       have i₂ := eq47 sF5 x
       grind)
    | exact superpose eq47 eq416192
    | exact resolve eq416192 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq416192
  have eq417487 : (k (M.op x y) (τ (σ y))) = (M.op (k (M.op x y) (τ (σ y))) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq416201 eq2976
    | exact resolve eq2976 eq416201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq938515 : (τ (σ y)) = (M.op (k (M.op x y) (τ (σ y))) (k (τ (σ y)) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq417487 eq266349
    | exact resolve eq266349 eq417487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266349 eq417487
  have eq938533 : (τ (σ y)) = (M.op (k (M.op x y) (τ (σ y))) (k (τ (σ y)) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by grind
  clear eq938515
  have eq1059044 : (τ (σ y)) = (M.op (k (M.op x y) (τ (σ y))) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq416201 eq938533
    | exact resolve eq938533 eq416201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416201 eq938533
  have eq1059068 : (τ (σ y)) = (M.op (k (M.op x y) (τ (σ y))) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by grind
  clear eq1059044
  have eq1601670 : (σ y) = (k (σ y) (k (k (σ y) (σ x)) (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq392053 eq375526
    | exact resolve eq375526 eq392053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375526 eq392053
  have eq1601682 : (σ y) = (k (σ y) (k (k (σ y) (σ x)) (σ y))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by grind
  clear eq1601670
  have eq1601715 : (τ (σ y)) = (k (τ (σ y)) (τ (k (k (σ y) (σ x)) (σ y)))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq1601682 eq123
    | exact resolve eq123 eq1601682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601682
  have eq1601725 : (τ (σ y)) = (k (τ (σ y)) (k (τ (k (σ y) (σ x))) (τ (σ y)))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq1601715
       have i₂ := eq123 sF5 (k sF5 sF4)
       grind)
    | exact superpose eq123 eq1601715
    | exact resolve eq1601715 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601715
  have eq1601727 : (τ (σ y)) = (k (τ (σ y)) (k (k (τ (σ y)) (τ (σ x))) (τ (σ y)))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq1601725
       have i₂ := eq123 sF4 sF5
       grind)
    | exact superpose eq123 eq1601725
    | exact resolve eq1601725 eq123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq1601725
  have eq1601729 : (τ (σ y)) = (k (τ (σ y)) (k (M.op x y) (τ (σ y)))) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq94731 eq1601727
    | exact resolve eq1601727 eq94731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94731 eq1601727
  have eq1603810 : (τ (σ x)) = (M.op (τ (σ y)) (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq1059068 eq408401
    | exact resolve eq408401 eq1059068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408401 eq1059068
  have eq1603843 : (τ (σ x)) = (M.op (τ (σ y)) (k (τ (σ x)) (τ (σ x)))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by grind
  clear eq1603810
  have eq1603888 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op X0 (τ (σ x))) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | exact superpose eq1603843 eq33408
    | exact resolve eq33408 eq1603843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33408 eq1603843
  have eq1603933 : ∀ X0 : G, (τ (σ y)) = (M.op (M.op X0 (τ (σ x))) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    intro X0
    first
    | (have j0 := eq1603888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603888
  have eq1603957 : (τ (σ y)) = (M.op (k (τ (σ x)) (τ (σ x))) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq7044 eq1603933
    | exact resolve eq1603933 eq7044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7044 eq1603933
  have eq1604117 : (M.op (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq1603957 eq6764
    | exact resolve eq6764 eq1603957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6764 eq1603957
  have eq1604213 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq42 eq1604117
    | exact resolve eq1604117 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq1604117
  have eq1604396 : (M.op x y) = (k (M.op x y) (τ (σ y))) ∨ (M.op x y) = (k (M.op x y) (τ (σ y))) := by
    first
    | exact superpose eq1604213 eq371328
    | exact resolve eq371328 eq1604213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371328 eq1604213
  have eq1604442 : (M.op x y) = (k (M.op x y) (τ (σ y))) := by grind
  clear eq1604396
  have eq1604525 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by
    first
    | exact superpose eq1604442 eq1601729
    | exact resolve eq1601729 eq1604442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601729 eq1604442
  have eq1604551 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) := by grind
  clear eq1604525
  have eq1604614 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq1604551 eq15
    | exact resolve eq15 eq1604551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604551
  have eq1604626 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq1604614
    | exact resolve eq1604614 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1604614
  have eq1604627 : (σ (τ (σ y))) = (k (σ (τ (σ y))) (k (σ y) (σ x))) := by
    first
    | exact superpose eq94317 eq1604626
    | exact resolve eq1604626 eq94317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604626
  have eq1604628 : (σ y) = (k (σ y) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq1604627
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq1604627
    | exact resolve eq1604627 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1604627
  have eq1955013 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq53120 eq33
    | exact resolve eq33 eq53120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53120
  have eq1955160 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq1955013
       have r₂ := eq94317
       grind)
    | exact resolve eq1955013 eq94317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94317 eq1955013
  have eq1955310 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1955160 eq51507
    | exact resolve eq51507 eq1955160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51507
  have eq1955792 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq1955160 eq1604628
    | exact resolve eq1604628 eq1955160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604628
  have eq1956014 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1955310
       have r₂ := eq1955792
       grind)
    | exact resolve eq1955310 eq1955792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955310
  have eq1956137 : (σ y) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq1956014 eq441
    | exact resolve eq441 eq1956014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441
  have eq1956734 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq1956137
       have r₂ := eq1955792
       grind)
    | exact resolve eq1956137 eq1955792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955792 eq1956137
  have eq1956742 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1955160 eq1956734
    | exact resolve eq1956734 eq1955160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1955160 eq1956734
  have eq1956750 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1956742 eq33
    | exact resolve eq33 eq1956742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq1956742
  have eq1960473 : False := by grind
  exact eq1960473

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pxy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq9 X1 (M.op x (M.op X1 x)) X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq9
    | exact resolve eq9 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq131 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq13
    | (have j0 := eq13 X1 X1
       have j1 := eq131 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq131 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq131 X0 X0
       grind)
    | exact resolve eq13 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq131 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq131 X0 X1
       grind)
    | (have r₁ := eq12 (M.op X1 X1) X1
       have r₂ := eq131 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 X2 : G, (M.op X1 X0) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = X2 ∨ (M.op X1 X2) = (k X2 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq131 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq131 X0 X0
       grind)
    | exact superpose eq131 eq13
    | (have j0 := eq13 X2 X1
       have j1 := eq131 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq131 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq131 X0 X0
       grind)
    | exact resolve eq13 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq214 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq191 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq215 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq190 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq380 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (M.op X0 X0) X1
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq40
    | exact resolve eq40 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq215 X0 X1
       have j1 := eq214 X0 X1
       grind)
    | (have r₁ := eq215 X0 X1
       have r₂ := eq214 X0 X1
       grind)
    | (have r₁ := eq215 (M.op X1 X1) X1
       have r₂ := eq214 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq215 X0 X1
       have r₂ := eq214 (k X0 X1) X1
       grind)
    | exact resolve eq215 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq215
  have eq515 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (k X0 X1)) (k X0 X1)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq463 X0 X1
       grind)
    | exact superpose eq463 eq9
    | (have j1 := eq463 X0 X1
       grind)
    | exact resolve eq9 eq463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq532 : ∀ X0 X1 : G, (M.op (k X0 X1) (k X0 X1)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq515 X0 X1 x
       have i₂ := eq380 (k X0 X1) x
       grind)
    | exact superpose eq380 eq515
    | (have j0 := eq515 X0 X1 x
       grind)
    | exact resolve eq515 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq515
  have eq724 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X2 (M.op X1 X0))) (M.op (M.op X3 X1) (M.op X3 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq29 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq29
    | exact resolve eq29 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 X1 X1 X2 (M.op X1 X1)
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq29
    | exact resolve eq29 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X2 (M.op X0 X1))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq40 X0 (M.op (M.op X2 (M.op X0 X1)) (M.op X2 (M.op X0 X1))) X3
       have i₂ := eq29 X0 X0 X2 X1
       grind)
    | exact superpose eq29 eq40
    | exact resolve eq40 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40
  have eq1599 : ∀ X1 X2 : G, (M.op X1 X1) = (M.op (M.op X1 X2) X1) := by
    intro X1 X2
    first
    | (have i₁ := eq760 X1 X2 (M.op X1 X2) (M.op x (M.op (M.op X1 X2) x))
       have i₂ := eq9 (M.op X1 X2) x x
       grind)
    | exact superpose eq9 eq760
    | exact resolve eq760 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq1684 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1599 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq32 X0 X1
       grind)
    | exact superpose eq32 eq1599
    | exact resolve eq1599 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq1599
  have eq1796 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq198 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq1800 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1796 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1796 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1796 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq2851 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1800 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3912 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq729 X0 X1 X2
       have i₂ := eq1684 X0 X1
       grind)
    | exact superpose eq1684 eq729
    | exact resolve eq729 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq4923 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq532 X1 X0
       have i₂ := eq1800 X0 X1
       grind)
    | exact superpose eq1800 eq532
    | (have j0 := eq532 X1 X0
       have j1 := eq1800 X0 X1
       grind)
    | exact resolve eq532 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532 eq1800
  have eq5044 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq4923 X0 X1
       have j1 := eq2851 X1 X0
       grind)
    | (have r₁ := eq4923 X0 X1
       have r₂ := eq2851 X0 X1
       grind)
    | (have r₁ := eq4923 X1 X0
       have r₂ := eq2851 X0 X1
       grind)
    | exact resolve eq4923 eq2851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4923
  have eq5045 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5044 X0 X1
       have i₂ := eq1684 X1 X0
       grind)
    | exact superpose eq1684 eq5044
    | (have j0 := eq5044 X0 X1
       grind)
    | exact resolve eq5044 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5044
  have eq7760 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X2 (M.op X1 X0))) (M.op X1 (M.op X3 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq724 X0 X1 X2 X3 X4
       have i₂ := eq1684 X1 X3
       grind)
    | exact superpose eq1684 eq724
    | exact resolve eq724 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724 eq1684
  have eq7833 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op (M.op X2 X1) (M.op X2 (M.op X3 X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq7760 X1 X2 X1 X3 (M.op x X1)
       have i₂ := eq3912 X1 X2 x
       grind)
    | exact superpose eq3912 eq7760
    | exact resolve eq7760 eq3912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3912 eq7760
  have eq8081 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7833 (M.op X0 X0) X0 X1
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq7833
    | exact resolve eq7833 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq7833
  have eq8369 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq8081 X1 X0
       have i₂ := eq5045 X0 X1
       grind)
    | exact superpose eq5045 eq8081
    | (have j1 := eq5045 X0 X1
       grind)
    | exact resolve eq8081 eq5045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5045 eq8081
  have eq8461 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq8369 X0 X1
       have j1 := eq2851 X1 X0
       grind)
    | (have r₁ := eq8369 X0 X1
       have r₂ := eq2851 X0 X1
       grind)
    | (have r₁ := eq8369 X1 X0
       have r₂ := eq2851 X0 X1
       grind)
    | exact resolve eq8369 eq2851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2851 eq8369
  have eq8586 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq8461 (σ X1) (σ X0)
       grind)
    | exact superpose eq8461 eq15
    | exact resolve eq15 eq8461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8619 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8586 X0 X1
       have i₂ := eq8461 X1 X0
       grind)
    | exact superpose eq8461 eq8586
    | exact resolve eq8586 eq8461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461 eq8586
  have eq8756 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8619 x y
       grind)
    | exact superpose eq8619 eq16
    | (have r₁ := eq16
       have r₂ := eq8619 x y
       grind)
    | exact resolve eq16 eq8619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8619
  have eq8790 : False := by grind
  exact eq8790

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq77 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
  clear eq45
  have eq84 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq77
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq21 eq86
    | exact resolve eq86 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq384 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3260 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq384 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq384
    | exact resolve eq384 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq384
  have eq4284 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq74
    | (have j0 := eq74 x
       grind)
    | exact resolve eq74 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq4299 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq4284
  have eq4303 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq4299
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq4299
    | exact resolve eq4299 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4299
  have eq4317 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq4303
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq4303 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303
  have eq4321 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq4317 eq50
    | exact resolve eq50 eq4317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq14199 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4317 eq84
    | exact resolve eq84 eq4317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq20945 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq14199
       grind)
    | exact superpose eq14199 eq16
    | exact resolve eq16 eq14199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14199
  have eq21011 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4321 eq20945
    | exact resolve eq20945 eq4321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20945
  have eq21018 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq21011
       have r₂ := eq13 x x
       grind)
    | exact resolve eq21011 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21011
  have eq21019 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq21018
       grind)
    | exact superpose eq21018 eq44
    | exact resolve eq44 eq21018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq21059 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq4317 eq21019
    | exact resolve eq21019 eq4317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4317 eq21019
  have eq30218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq87 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq30219 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq27 eq30218
    | exact resolve eq30218 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30218
  have eq30230 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq30219
       have r₂ := eq28
       grind)
    | exact resolve eq30219 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30219
  have eq30264 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30230 eq3260
    | exact resolve eq3260 eq30230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32570 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30264 eq30230
    | exact resolve eq30230 eq30264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30230 eq30264
  have eq32609 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq32570
  have eq32616 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32609 eq4321
    | exact resolve eq4321 eq32609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321 eq32609
  have eq32674 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq32616
       have i₂ := eq21018
       grind)
    | exact superpose eq21018 eq32616
    | exact resolve eq32616 eq21018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21018 eq32616
  have eq32683 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq30 eq32674
    | exact resolve eq32674 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32674
  have eq32684 : y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq32683
  have eq32719 : (M.op x x) = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3260 x y
       have i₂ := eq32684
       grind)
    | exact superpose eq32684 eq3260
    | exact resolve eq3260 eq32684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3260
  have eq34562 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq32684
       have i₂ := eq32719
       grind)
    | exact superpose eq32719 eq32684
    | exact resolve eq32684 eq32719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32684 eq32719
  have eq34603 : y = (M.op x x) := by grind
  clear eq34562
  have eq34616 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq21059
       have i₂ := eq34603
       grind)
    | exact superpose eq34603 eq21059
    | exact resolve eq21059 eq34603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21059
  have eq34627 : x = (M.op x y) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq34603
       grind)
    | exact superpose eq34603 eq54
    | exact resolve eq54 eq34603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34603
  have eq34664 : x = (M.op x y) := by
    first
    | (have i₁ := eq34627
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34627
    | exact resolve eq34627 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq34627
  have eq34667 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq34616
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34616
    | exact resolve eq34616 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq34616
  have eq34677 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq34664 eq21
    | exact resolve eq21 eq34664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq34664
  have eq34902 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq34677
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq34677
    | exact resolve eq34677 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq34677
  have eq34972 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq34902 eq27
    | exact resolve eq27 eq34902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq35581 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq34902 eq34667
    | exact resolve eq34667 eq34902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34667 eq34902
  have eq35594 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq35581 eq54
    | exact resolve eq54 eq35581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq35581
  have eq36519 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35594 eq34972
    | exact resolve eq34972 eq35594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34972 eq35594
  have eq36520 : False := by grind
  exact eq36520

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq40 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq118 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq40 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq121 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq118 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq118 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq118 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq813 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq121
  have eq823 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq813 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq813
  have eq4294 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq823 (σ X0) (σ X1)
       grind)
    | exact superpose eq823 eq15
    | exact resolve eq15 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4308 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4294 X0 X1
       have i₂ := eq823 X0 X1
       grind)
    | exact superpose eq823 eq4294
    | exact resolve eq4294 eq823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823 eq4294
  have eq4320 : False := by grind
  exact eq4320

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxx_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq177 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq180 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq180
    | (have j0 := eq180 y x
       grind)
    | exact resolve eq180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ y) (σ x)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq180 X0 X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1))) X1
       have r₂ := eq180 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq195 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq584 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq583 (M.op X0 X0)
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq583
    | exact resolve eq583 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq660 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq662 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq177
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq666 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq1147 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1151 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1147 X0 X1
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq1147
    | exact resolve eq1147 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq1180 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1151 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1151
    | (have j0 := eq1151 y x
       grind)
    | exact resolve eq1151 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq1151
    | (have j0 := eq1151 (σ y) (σ x)
       grind)
    | exact resolve eq1151 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1218 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq190
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq190
    | exact resolve eq190 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq1220 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) y) y
       have r₂ := eq1180
       grind)
    | exact resolve eq13 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1224 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq180 y X0
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq180
    | exact resolve eq180 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1230 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq11
    | exact resolve eq11 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1234 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq1230
  have eq1247 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ y) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1183 eq16
    | exact resolve eq16 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1467 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq191 eq1247
    | exact resolve eq1247 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq1247
  have eq1489 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1467 eq11
    | (have j0 := eq11 (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq11 eq1467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1467
  have eq1495 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1489
       have i₂ := eq180 sF4 sF4
       grind)
    | exact superpose eq180 eq1489
    | exact resolve eq1489 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489
  have eq1496 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1495
  have eq1524 : (k y (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1496 eq107
    | exact resolve eq107 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1496
  have eq1573 : y = (M.op (M.op x y) (k y y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1234 eq1218
    | exact resolve eq1218 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1583 : y = (M.op (k y y) (k y y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1234 eq1224
    | exact resolve eq1224 eq1234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224 eq1234
  have eq1635 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq660
       grind)
    | exact superpose eq660 eq40
    | exact resolve eq40 eq660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq1636 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1635
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1635
    | exact resolve eq1635 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1635
  have eq1638 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1636
    | exact resolve eq1636 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1640 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1638
       have i₂ := eq1180
       grind)
    | exact superpose eq1180 eq1638
    | exact resolve eq1638 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq1669 : (k y y) = (M.op y (M.op (k y y) (k y y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1573 eq180
    | exact resolve eq180 eq1573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1573
  have eq1671 : (k y y) = (M.op y y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1583 eq1669
    | exact resolve eq1669 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583 eq1669
  have eq1674 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq1220 y
       grind)
    | (have r₁ := eq1671
       have r₂ := eq1220 y
       grind)
    | exact resolve eq1671 eq1220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1220 eq1671
  have eq1687 : (k y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1180
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq1180
    | exact resolve eq1180 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180
  have eq1700 : (k y y) = (M.op (k y y) y) := by
    first
    | (have i₁ := eq1151 y y
       have i₂ := eq1674
       grind)
    | exact superpose eq1674 eq1151
    | exact resolve eq1151 eq1674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674
  have eq2561 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1640 eq662
    | exact resolve eq662 eq1640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq2570 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2561
       have r₂ := eq27
       grind)
    | exact resolve eq2561 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2576 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1687 eq2570
    | exact resolve eq2570 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570
  have eq2600 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2576 eq1151
    | exact resolve eq1151 eq2576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576
  have eq2609 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2600
    | exact resolve eq2600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600
  have eq2610 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2609
  have eq2637 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1700
       have i₂ := eq2610
       grind)
    | exact superpose eq2610 eq1700
    | exact resolve eq1700 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610
  have eq2658 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2637
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2637
    | exact resolve eq2637 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2637
  have eq2659 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2658
  have eq2667 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2659 eq27
    | exact resolve eq27 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2674 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2659 eq1183
    | exact resolve eq1183 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq2687 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2674
    | exact resolve eq2674 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2674
  have eq2688 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2659 eq2687
    | exact resolve eq2687 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2687
  have eq2707 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2688 eq584
    | exact resolve eq584 eq2688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2712 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2688 eq180
    | exact resolve eq180 eq2688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq2688
  have eq2752 : (σ (M.op x y)) = (σ y) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2707 eq1640
    | exact resolve eq1640 eq2707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640 eq2707
  have eq2758 : (σ (M.op x y)) = (σ y) ∨ x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq2752
  have eq2763 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1687 eq2758
    | exact resolve eq2758 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2758
  have eq3399 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1700
       have i₂ := eq2763
       grind)
    | exact superpose eq2763 eq1700
    | exact resolve eq1700 eq2763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700 eq2763
  have eq3421 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3399
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3399
    | exact resolve eq3399 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399
  have eq3422 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq3421
  have eq3430 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3422 eq28
    | exact resolve eq28 eq3422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq3451 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3422 eq2667
    | exact resolve eq2667 eq3422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2667 eq3422
  have eq3452 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq3451
  have eq3467 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq3430
    | exact resolve eq3430 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3430
  have eq3477 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3467
       grind)
    | exact superpose eq3467 eq18
    | exact resolve eq18 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3511 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (τ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1524
       have i₂ := eq3467
       grind)
    | exact superpose eq3467 eq1524
    | exact resolve eq1524 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq3519 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1687
       have i₂ := eq3467
       grind)
    | exact superpose eq3467 eq1687
    | exact resolve eq1687 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3559 : (τ (σ x)) = (k (M.op x y) (τ (M.op (σ x) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2659 eq3511
    | exact resolve eq3511 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3511
  have eq3566 : x = (k (M.op x y) (τ (M.op (σ x) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3559
    | exact resolve eq3559 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3559
  have eq3569 : x = (k (M.op x y) (τ (M.op (σ x) (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2659 eq3566
    | exact resolve eq3566 eq2659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659 eq3566
  have eq3570 : x = (k (M.op x y) (τ (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3569
       have r₂ := eq3452
       grind)
    | exact resolve eq3569 eq3452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3452 eq3569
  have eq3571 : x = (k (M.op x y) (τ (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2712 eq3570
    | exact resolve eq3570 eq2712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2712 eq3570
  have eq3572 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq3571
    | exact resolve eq3571 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq3571
  have eq3573 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3467 eq3572
    | exact resolve eq3572 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467 eq3572
  have eq3611 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3573 eq722
    | (have j0 := eq722 (M.op x y)
       grind)
    | exact resolve eq722 eq3573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3615 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3519 eq3611
    | exact resolve eq3611 eq3519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3519 eq3611
  have eq3620 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3573 eq3615
    | exact resolve eq3615 eq3573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3573 eq3615
  have eq3621 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq3620
  have eq3639 : (M.op x x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3621 eq1151
    | exact resolve eq1151 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3643 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3621 eq3639
    | exact resolve eq3639 eq3621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3621 eq3639
  have eq3677 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq177 x
       have i₂ := eq3643
       grind)
    | exact superpose eq3643 eq177
    | exact resolve eq177 eq3643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3643
  have eq3702 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3477 eq3677
    | exact resolve eq3677 eq3477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3477 eq3677
  have eq3703 : x = (M.op x y) := by grind
  clear eq3702
  have eq3707 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3703
       grind)
    | exact superpose eq3703 eq18
    | exact resolve eq18 eq3703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3708 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq3703
       grind)
    | exact superpose eq3703 eq22
    | exact resolve eq22 eq3703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq3703
  have eq3723 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3708 eq20
    | exact resolve eq20 eq3708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3708
  have eq4324 : (M.op x y) = (k y y) := by
    first
    | exact superpose eq3707 eq1687
    | exact resolve eq1687 eq3707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687 eq3707
  have eq4426 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq4324
       grind)
    | exact superpose eq4324 eq40
    | exact resolve eq40 eq4324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4324
  have eq4443 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq4426
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4426
    | exact resolve eq4426 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4426
  have eq4449 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq4443
    | exact resolve eq4443 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4443
  have eq4454 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq3723 eq4449
    | exact resolve eq4449 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4449
  have eq4553 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq4454 eq722
    | (have j0 := eq722 (σ y)
       grind)
    | exact resolve eq722 eq4454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq4556 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq4454 eq703
    | (have j0 := eq703 (σ y) (σ y)
       grind)
    | exact resolve eq703 eq4454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq4557 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq4556
  have eq6028 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq4553 eq584
    | exact resolve eq584 eq4553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq4553
  have eq6043 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4454 eq6028
    | exact resolve eq6028 eq4454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454 eq6028
  have eq6065 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6043 eq1151
    | exact resolve eq1151 eq6043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq6067 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6043 eq6065
    | exact resolve eq6065 eq6043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6043 eq6065
  have eq6091 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6067 eq177
    | exact resolve eq177 eq6067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq6067
  have eq6117 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq6091
    | exact resolve eq6091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6091
  have eq6123 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq6117 eq27
    | exact resolve eq27 eq6117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6117
  have eq6157 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq6123
       have r₂ := eq3723
       grind)
    | exact resolve eq6123 eq3723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6123
  have eq6165 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6157 eq26
    | exact resolve eq26 eq6157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq6225 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6157 eq4557
    | (have r₁ := eq4557
       have r₂ := eq6157
       grind)
    | exact resolve eq4557 eq6157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557 eq6157
  have eq6227 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6225
  have eq6262 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6227 eq6165
    | exact resolve eq6165 eq6227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6165 eq6227
  have eq6306 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq6262 eq27
    | exact resolve eq27 eq6262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6262
  have eq6336 : False := by grind
  exact eq6336

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyx_pxx_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq72 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq75 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq50
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq50
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq50 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq75
  have eq78 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq72
  have eq87 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq247 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq550 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq54
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq54 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq562 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq550 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq567 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (M.op (σ X1) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq555 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq555
    | (have j0 := eq555 X0 X1
       grind)
    | exact resolve eq555 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq3257 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq418
    | exact resolve eq418 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq418
  have eq3285 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3257
    | (have j0 := eq3257 (σ y) (σ x)
       grind)
    | exact resolve eq3257 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3704 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq562 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq562
    | (have j0 := eq562 (τ X0)
       grind)
    | exact resolve eq562 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq562
  have eq3725 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3704 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3704
    | (have j0 := eq3704 X0
       grind)
    | exact resolve eq3704 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq3737 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3725 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3725
    | (have j0 := eq3725 X0
       grind)
    | exact resolve eq3725 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq23653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq23654 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23653
    | exact resolve eq23653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23653
  have eq23665 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23654
       have r₂ := eq28
       grind)
    | exact resolve eq23654 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23654
  have eq23692 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23665 eq3257
    | exact resolve eq3257 eq23665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25010 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23692 eq23665
    | exact resolve eq23665 eq23692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23665 eq23692
  have eq25045 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq25010
  have eq25059 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq25045 eq54
    | exact resolve eq54 eq25045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25045
  have eq25089 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq25059
    | exact resolve eq25059 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25059
  have eq25119 : (M.op x x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3257 x y
       have i₂ := eq25089
       grind)
    | exact superpose eq25089 eq3257
    | exact resolve eq3257 eq25089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3257
  have eq26871 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq25089
       have i₂ := eq25119
       grind)
    | exact superpose eq25119 eq25089
    | exact resolve eq25089 eq25119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25089 eq25119
  have eq26908 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq26871
  have eq26915 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq26908
       grind)
    | exact superpose eq26908 eq78
    | exact resolve eq78 eq26908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq26924 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54 x
       have i₂ := eq26908
       grind)
    | exact superpose eq26908 eq54
    | exact resolve eq54 eq26908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq26926 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq26908
       grind)
    | exact superpose eq26908 eq65
    | exact resolve eq65 eq26908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26908
  have eq26956 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26924
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26924
    | exact resolve eq26924 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26924
  have eq26958 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26915
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq26915
    | exact resolve eq26915 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26915
  have eq26963 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26956 eq247
    | exact resolve eq247 eq26956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq26969 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26956 eq3285
    | exact resolve eq3285 eq26956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq27020 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq26969
    | exact resolve eq26969 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26969
  have eq28488 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27020 eq26963
    | exact resolve eq26963 eq27020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26963 eq27020
  have eq28526 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq28488
  have eq28531 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26956 eq28526
    | exact resolve eq28526 eq26956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26956 eq28526
  have eq28561 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq28531
  have eq28564 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28561 eq77
    | exact resolve eq77 eq28561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq28561
  have eq28607 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq28564
    | exact resolve eq28564 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28564
  have eq31853 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26958 eq50
    | exact resolve eq50 eq26958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31872 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26958 eq3737
    | (have j0 := eq3737 (σ x)
       grind)
    | exact resolve eq3737 eq26958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26958
  have eq31885 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq31872
    | exact resolve eq31872 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31872
  have eq31886 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq31885
  have eq31895 : y = (k x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq31853
    | exact resolve eq31853 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31853
  have eq31962 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq31886 eq65
    | exact resolve eq65 eq31886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31886
  have eq32191 : (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq31962 eq50
    | exact resolve eq50 eq31962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31962
  have eq32242 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq29 eq32191
    | exact resolve eq32191 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32191
  have eq32405 : x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq31895
       have i₂ := eq32242
       grind)
    | exact superpose eq32242 eq31895
    | exact resolve eq31895 eq32242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31895 eq32242
  have eq32429 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq32405
  have eq32453 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq32429 eq28
    | exact resolve eq28 eq32429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32429
  have eq37998 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3737 x
       have i₂ := eq28607
       grind)
    | exact superpose eq28607 eq3737
    | (have j0 := eq3737 x
       grind)
    | exact resolve eq3737 eq28607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3737
  have eq38017 : x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq37998
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq37998
    | exact resolve eq37998 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37998
  have eq38018 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq38017
  have eq38921 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq65 x
       have i₂ := eq38018
       grind)
    | exact superpose eq38018 eq65
    | exact resolve eq65 eq38018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38018
  have eq39341 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28607
       have i₂ := eq38921
       grind)
    | exact superpose eq38921 eq28607
    | exact resolve eq28607 eq38921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28607 eq38921
  have eq39367 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq39341
  have eq39656 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39367 eq30
    | exact resolve eq30 eq39367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq39367
  have eq39927 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq39656
    | exact resolve eq39656 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39656
  have eq39928 : x = (M.op x y) ∨ x = y := by grind
  clear eq39927
  have eq39929 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq39928 eq21
    | exact resolve eq21 eq39928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39928
  have eq40146 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq39929
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq39929
    | exact resolve eq39929 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39929
  have eq40147 : x = y := by
    first
    | (have r₁ := eq40146
       have r₂ := eq32453
       grind)
    | exact resolve eq40146 eq32453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32453 eq40146
  have eq40148 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq40147
       grind)
    | exact superpose eq40147 eq19
    | exact resolve eq19 eq40147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq40149 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq40147
       grind)
    | exact superpose eq40147 eq25
    | exact resolve eq25 eq40147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq40280 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq26926
       have i₂ := eq40147
       grind)
    | exact superpose eq40147 eq26926
    | exact resolve eq26926 eq40147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26926 eq40147
  have eq40374 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40149
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq40149
    | exact resolve eq40149 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40149
  have eq40379 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40374 eq27
    | exact resolve eq27 eq40374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq40374
  have eq40776 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq40379 eq65
    | exact resolve eq65 eq40379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq43980 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq567 x x
       have i₂ := eq40280
       grind)
    | exact superpose eq40280 eq567
    | (have j0 := eq567 x x
       grind)
    | exact resolve eq567 eq40280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq40280
  have eq43989 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43980
  have eq43990 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq43989
  have eq44002 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43990
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq43990
    | exact resolve eq43990 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43990
  have eq44024 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq40379 eq44002
    | exact resolve eq44002 eq40379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40379 eq44002
  have eq44025 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44024
  have eq44044 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq44025 eq28
    | exact resolve eq28 eq44025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq44127 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq44025 eq40776
    | exact resolve eq40776 eq44025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40776 eq44025
  have eq44822 : (τ (σ x)) = (k x x) := by
    first
    | exact superpose eq44127 eq50
    | exact resolve eq50 eq44127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq44127
  have eq44882 : x = (k x x) := by
    first
    | exact superpose eq29 eq44822
    | exact resolve eq44822 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq44822
  have eq44923 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq44882
       grind)
    | exact superpose eq44882 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq44882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44882
  have eq44924 : x = (M.op x x) := by grind
  clear eq44923
  have eq44939 : x = (M.op x y) := by
    first
    | (have i₁ := eq44924
       have i₂ := eq40148
       grind)
    | exact superpose eq40148 eq44924
    | exact resolve eq44924 eq40148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40148 eq44924
  have eq44976 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq44939 eq21
    | exact resolve eq21 eq44939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq44939
  have eq45252 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq44976
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq44976
    | exact resolve eq44976 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq44976
  have eq45331 : False := by grind
  exact eq45331
