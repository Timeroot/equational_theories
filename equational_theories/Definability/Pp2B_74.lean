import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_y_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq174 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq16 X2 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq178 x x X2 X3 X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq185 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq182 x x X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq182
    | exact resolve eq182 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq191 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 (M.op X0 x)
       have i₂ := eq179 X0 x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq179 x x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq248 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq222 eq185
    | exact resolve eq185 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq185 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 x (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq185 x
       grind)
    | exact resolve eq13 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq260 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | (have j0 := eq255 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq263 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq222 eq260
    | exact resolve eq260 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq271 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (k (M.op (M.op x y) y) X0) = (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq191 eq13
    | (have j0 := eq13 (M.op (M.op x y) y) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) y) (M.op (M.op x y) y)
       have r₂ := eq191 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq191 eq271
    | (have j0 := eq271 X0
       grind)
    | (have r₁ := eq271 (M.op X0 (M.op (M.op x y) y))
       have r₂ := eq191 X0
       grind)
    | exact resolve eq271 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq326 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | (have i₁ := eq197 X0 X0
       have i₂ := eq263 X0
       grind)
    | exact superpose eq263 eq197
    | exact resolve eq197 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq329 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) ≠ X0 ∨ (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq263 X0
       grind)
    | exact superpose eq263 eq13
    | exact resolve eq13 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq919 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq263 X0
       grind)
    | exact superpose eq263 eq11
    | exact resolve eq11 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq950 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 ∨ (M.op X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq248 x
       have i₂ := eq11 (M.op sF0 y) x
       grind)
    | exact superpose eq11 eq248
    | (have j1 := eq11 (M.op (M.op x y) y) X0
       grind)
    | exact resolve eq248 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq958 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
  have eq966 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq977 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq919 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919
  have eq988 : ∀ X0 : G, (M.op (M.op x y) y) = X0 ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq191 eq950
    | (have j0 := eq950 X0
       grind)
    | exact resolve eq950 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq1007 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq977 X0
       have j1 := eq329 X0
       grind)
    | (have r₁ := eq977 X0
       have r₂ := eq329 X0
       grind)
    | exact resolve eq977 eq329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329 eq977
  have eq1019 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq988 X0
       have j1 := eq277 X0
       grind)
    | (have r₁ := eq988 X0
       have r₂ := eq277 X0
       grind)
    | (have r₁ := eq988 (M.op (M.op x y) y)
       have r₂ := eq277 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq988 X0
       have r₂ := eq277 (k (M.op (M.op x y) y) X0)
       grind)
    | exact resolve eq988 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1034 : ∀ X0 : G, (M.op (M.op x y) y) = X0 ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq191 eq1019
    | (have j0 := eq1019 X0
       grind)
    | exact resolve eq1019 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1045 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq1034 (k (M.op (M.op x y) y) X0)
       have j1 := eq277 X0
       grind)
    | (have r₁ := eq1034 X0
       have r₂ := eq277 X0
       grind)
    | (have r₁ := eq1034 (M.op (M.op x y) y)
       have r₂ := eq277 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq1034 X0
       have r₂ := eq277 (k (M.op (M.op x y) y) X0)
       grind)
    | exact resolve eq1034 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq1034
  have eq1076 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq263 (M.op sF0 y)
       have i₂ := eq1007 (M.op sF0 y)
       grind)
    | exact superpose eq1007 eq263
    | exact resolve eq263 eq1007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1140 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 X0
       have i₂ := eq1076 X0
       grind)
    | exact superpose eq1076 eq179
    | exact resolve eq179 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1169 : ∀ X0 : G, (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq1045 eq517
    | exact resolve eq517 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq1045
  have eq1180 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1140 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1140
    | exact resolve eq1140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3069 : (M.op (M.op x y) y) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq1169 eq326
    | exact resolve eq326 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326
  have eq3087 : (M.op (M.op x y) y) = (k (τ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq3069
       have i₂ := eq263 (τ (M.op sF0 y))
       grind)
    | exact superpose eq263 eq3069
    | exact resolve eq3069 eq263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263 eq3069
  have eq3096 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq1169 eq3087
    | exact resolve eq3087 eq1169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169 eq3087
  have eq3111 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3096 eq14
    | exact resolve eq14 eq3096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4829 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq958
       grind)
    | exact superpose eq958 eq40
    | exact resolve eq40 eq958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq958
  have eq4830 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4829
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4829
    | exact resolve eq4829 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4829
  have eq4832 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq4830
    | exact resolve eq4830 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4830
  have eq4834 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4832
       have i₂ := eq1076 x
       grind)
    | exact superpose eq1076 eq4832
    | exact resolve eq4832 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4832
  have eq32006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4834 eq966
    | exact resolve eq966 eq4834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966 eq4834
  have eq32015 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq32006
       have r₂ := eq27
       grind)
    | exact resolve eq32006 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32006
  have eq32022 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq32015
       have i₂ := eq1076 sF2
       grind)
    | exact superpose eq1076 eq32015
    | exact resolve eq32015 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32015
  have eq32026 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32022 eq97
    | exact resolve eq97 eq32022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq32022
  have eq32057 : y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq32026
    | exact resolve eq32026 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32026
  have eq32058 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq32057
  have eq32075 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) (σ x))) ∨ y = (k x x) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | exact superpose eq32058 eq174
    | exact resolve eq174 eq32058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32086 : (M.op (M.op x y) y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32058 eq197
    | exact resolve eq197 eq32058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32093 : (σ y) = (M.op (M.op x y) y) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32058 eq32086
    | exact resolve eq32086 eq32058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32086
  have eq32104 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ y) (σ x))) ∨ y = (k x x) ∨ y = (M.op y x) := by
    intro X2
    first
    | (have i₁ := eq32075 x x X2
       have i₂ := eq197 x x
       grind)
    | (have i₁ := eq32075 x y X2
       have i₂ := eq197 X2 x
       grind)
    | exact superpose eq197 eq32075
    | (have j0 := eq32075 x y X2
       grind)
    | exact resolve eq32075 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32075
  have eq32119 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    intro X2
    first
    | exact superpose eq32058 eq32104
    | exact resolve eq32104 eq32058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32058 eq32104
  have eq32129 : ∀ X2 : G, (σ y) = (M.op X2 (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    intro X2
    first
    | exact superpose eq32093 eq32119
    | exact resolve eq32119 eq32093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32119
  have eq32205 : (σ y) = (τ (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32093 eq3096
    | exact resolve eq3096 eq32093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3096 eq32093
  have eq32246 : y = (k x x) ∨ y = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq32205
    | exact resolve eq32205 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq32205
  have eq32387 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1140 x
       have i₂ := eq32246
       grind)
    | exact superpose eq32246 eq1140
    | exact resolve eq1140 eq32246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq32390 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1180 x
       have i₂ := eq32246
       grind)
    | exact superpose eq32246 eq1180
    | exact resolve eq1180 eq32246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq32246
  have eq32404 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq32390
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32390
    | exact resolve eq32390 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32390
  have eq32405 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq32387
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq32387
    | exact resolve eq32387 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32387
  have eq32415 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq32404
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32404
    | exact resolve eq32404 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32404
  have eq32422 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq32415
    | exact resolve eq32415 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32415
  have eq32423 : y = (M.op y x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32405 eq32422
    | exact resolve eq32422 eq32405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32422
  have eq32439 : (M.op (M.op x y) y) = (M.op y x) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq197 y x
       have i₂ := eq32423
       grind)
    | exact superpose eq32423 eq197
    | exact resolve eq197 eq32423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32446 : y = (M.op (M.op x y) y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32423 eq32439
    | exact resolve eq32439 eq32423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32423 eq32439
  have eq32559 : y = (σ y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32446 eq3111
    | exact resolve eq3111 eq32446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32446
  have eq32599 : y = (σ y) ∨ y = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32559
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq32559
    | exact resolve eq32559 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32559
  have eq32600 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by grind
  clear eq32599
  have eq32658 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32600 eq27
    | exact resolve eq27 eq32600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32666 : (M.op (M.op x y) y) = (M.op (M.op x y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32600 eq222
    | exact resolve eq222 eq32600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq32600
  have eq32793 : (M.op (M.op x y) (σ y)) = (σ (M.op (M.op x y) (σ y))) ∨ y = (σ y) := by
    first
    | exact superpose eq32666 eq3111
    | exact resolve eq3111 eq32666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34899 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32405 eq3111
    | exact resolve eq3111 eq32405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32405
  have eq34948 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq34899
    | exact resolve eq34899 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34899
  have eq35000 : y = (M.op y x) ∨ y = (σ y) := by
    first
    | (have r₁ := eq34948
       have r₂ := eq32658
       grind)
    | exact resolve eq34948 eq32658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32658 eq34948
  have eq35044 : (M.op (M.op x y) y) = (M.op y x) ∨ y = (σ y) := by
    first
    | (have i₁ := eq197 y x
       have i₂ := eq35000
       grind)
    | exact superpose eq35000 eq197
    | exact resolve eq197 eq35000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35051 : (M.op y x) = (M.op (M.op x y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq32666 eq35044
    | exact resolve eq35044 eq32666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32666 eq35044
  have eq35068 : y = (M.op (M.op x y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq35000 eq35051
    | exact resolve eq35051 eq35000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35000 eq35051
  have eq35101 : y = (σ y) ∨ y = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq35068 eq32793
    | exact resolve eq32793 eq35068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32793 eq35068
  have eq35119 : y = (σ y) ∨ y = (σ y) := by grind
  clear eq35101
  have eq35139 : y = (σ y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq35119
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35119
    | exact resolve eq35119 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35119
  have eq35140 : y = (σ y) := by grind
  clear eq35139
  have eq35181 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35140
       grind)
    | exact superpose eq35140 eq18
    | exact resolve eq18 eq35140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq35182 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq35140
       grind)
    | exact superpose eq35140 eq24
    | exact resolve eq24 eq35140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq35185 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op X0 (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq191 X0
       have i₂ := eq35140
       grind)
    | exact superpose eq35140 eq191
    | exact resolve eq191 eq35140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq35276 : (M.op (M.op x y) (σ y)) = (σ (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq3111
       have i₂ := eq35140
       grind)
    | exact superpose eq35140 eq3111
    | exact resolve eq3111 eq35140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3111
  have eq35719 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq35181 eq16
    | exact resolve eq16 eq35181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35722 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq35181 eq176
    | exact resolve eq176 eq35181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq39087 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (M.op x y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq35719 X0 X0
       have i₂ := eq1076 X0
       grind)
    | exact superpose eq1076 eq35719
    | exact resolve eq35719 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076
  have eq39148 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq26 eq35719
    | (have j0 := eq35719 (σ x) (σ y)
       grind)
    | exact resolve eq35719 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35719
  have eq39637 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (M.op (M.op x y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq39087 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq39087
    | exact resolve eq39087 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70004 : (M.op x y) = (σ y) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32129 eq35181
    | exact resolve eq35181 eq32129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70055 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32129 eq26
    | (have j1 := eq32129 (σ x)
       grind)
    | exact resolve eq26 eq32129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32129
  have eq70083 : (σ y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq70055
       have i₂ := eq35140
       grind)
    | exact superpose eq35140 eq70055
    | exact resolve eq70055 eq35140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70055
  have eq70088 : (σ y) = (k x x) ∨ (M.op x y) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq70004
       have i₂ := eq35140
       grind)
    | exact superpose eq35140 eq70004
    | exact resolve eq70004 eq35140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70004
  have eq70137 : (σ y) = (k x x) ∨ (σ y) = (M.op (σ y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70083
       have i₂ := eq35140
       grind)
    | exact superpose eq35140 eq70083
    | exact resolve eq70083 eq35140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70083
  have eq70140 : (σ y) = (k x x) ∨ (σ y) = (M.op (σ y) x) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq70088
       have i₂ := eq35140
       grind)
    | exact superpose eq35140 eq70088
    | exact resolve eq70088 eq35140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70088
  have eq70302 : (M.op (M.op x y) (σ y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39087 x
       have i₂ := eq70137
       grind)
    | exact superpose eq70137 eq39087
    | exact resolve eq39087 eq70137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70304 : (M.op (M.op x y) (σ y)) = (M.op (σ x) (σ (σ y))) ∨ (σ y) = (M.op (σ y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39637 x
       have i₂ := eq70137
       grind)
    | exact superpose eq70137 eq39637
    | exact resolve eq39637 eq70137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39637 eq70137
  have eq70331 : (M.op (M.op x y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35182 eq70304
    | exact resolve eq70304 eq35182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70304
  have eq70332 : (σ y) = (M.op (σ y) x) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35181 eq70302
    | exact resolve eq70302 eq35181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70302
  have eq70360 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70331
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq70331
    | exact resolve eq70331 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq70331
  have eq70386 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq70360
    | exact resolve eq70360 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70360
  have eq70402 : (σ y) = (M.op (σ y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70332 eq70386
    | exact resolve eq70386 eq70332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70386
  have eq70422 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq70402 eq174
    | exact resolve eq174 eq70402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70443 : (M.op (M.op x y) (σ y)) = (M.op (σ y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70402 eq35722
    | exact resolve eq35722 eq70402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70447 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70402 eq70443
    | exact resolve eq70443 eq70402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70443
  have eq70464 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ y) x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq70422 x x X2
       have i₂ := eq197 x x
       grind)
    | (have i₁ := eq70422 x y X2
       have i₂ := eq197 X2 x
       grind)
    | exact superpose eq197 eq70422
    | (have j0 := eq70422 x y X2
       grind)
    | exact resolve eq70422 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70422
  have eq70483 : ∀ X2 : G, (M.op (M.op x y) (σ y)) = (M.op X2 (M.op (σ y) x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq70464 X2
       have i₂ := eq35140
       grind)
    | exact superpose eq35140 eq70464
    | exact resolve eq70464 eq35140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70464
  have eq70496 : ∀ X2 : G, (M.op X2 (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq70402 eq70483
    | exact resolve eq70483 eq70402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70402 eq70483
  have eq70505 : ∀ X2 : G, (σ y) = (M.op X2 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq70447 eq70496
    | exact resolve eq70496 eq70447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70447 eq70496
  have eq70961 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70505 eq26
    | (have j1 := eq70505 (σ x)
       grind)
    | exact resolve eq26 eq70505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70505
  have eq70971 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq70961
  have eq71005 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70971 eq39148
    | exact resolve eq39148 eq70971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39148
  have eq71006 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  have eq71008 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq71005
    | exact resolve eq71005 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq71005
  have eq71021 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70971 eq71008
    | exact resolve eq71008 eq70971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70971 eq71008
  have eq71057 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq71021 eq35185
    | exact resolve eq35185 eq71021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35185 eq71021
  have eq71251 : (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq71057 eq35181
    | exact resolve eq35181 eq71057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71057
  have eq71333 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq71251
       have r₂ := eq71006
       grind)
    | exact resolve eq71251 eq71006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71006 eq71251
  have eq71399 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq71333 eq27
    | exact resolve eq27 eq71333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq76311 : (M.op (M.op x y) (σ y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ y) x) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq39087 x
       have i₂ := eq70140
       grind)
    | exact superpose eq70140 eq39087
    | exact resolve eq39087 eq70140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39087 eq70140
  have eq76346 : (σ y) = (M.op (σ y) x) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq35181 eq76311
    | exact resolve eq76311 eq35181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76311
  have eq76555 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) x)) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq70332 eq174
    | exact resolve eq174 eq70332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq76576 : (M.op (M.op x y) (σ y)) = (M.op (σ y) x) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70332 eq35722
    | exact resolve eq35722 eq70332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35722 eq70332
  have eq76579 : (M.op x y) = (σ y) ∨ (M.op (M.op x y) (σ y)) = (M.op (σ y) x) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq71333 eq76576
    | exact resolve eq76576 eq71333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76576
  have eq76597 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ y) x)) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq76555 x x X2
       have i₂ := eq197 x x
       grind)
    | (have i₁ := eq76555 x y X2
       have i₂ := eq197 X2 x
       grind)
    | exact superpose eq197 eq76555
    | (have j0 := eq76555 x y X2
       grind)
    | exact resolve eq76555 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq76555
  have eq76602 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq76346 eq76579
    | exact resolve eq76579 eq76346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76579
  have eq76618 : ∀ X2 : G, (M.op (M.op x y) (σ y)) = (M.op X2 (M.op (σ y) x)) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq76597 X2
       have i₂ := eq35140
       grind)
    | exact superpose eq35140 eq76597
    | exact resolve eq76597 eq35140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35140 eq76597
  have eq76637 : ∀ X2 : G, (M.op x y) = (σ y) ∨ (M.op (M.op x y) (σ y)) = (M.op X2 (M.op (σ y) x)) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
    intro X2
    first
    | exact superpose eq71333 eq76618
    | (have j0 := eq76618 X2
       grind)
    | exact resolve eq76618 eq71333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71333 eq76618
  have eq76651 : ∀ X2 : G, (M.op x y) = (σ y) ∨ (σ y) = (M.op X2 (M.op (σ y) x)) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
    intro X2
    first
    | exact superpose eq76602 eq76637
    | exact resolve eq76637 eq76602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76602 eq76637
  have eq76660 : ∀ X2 : G, (σ y) = (M.op X2 (σ y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
    intro X2
    first
    | exact superpose eq76346 eq76651
    | exact resolve eq76651 eq76346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76346 eq76651
  have eq77268 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq76660 eq35181
    | exact resolve eq35181 eq76660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35181 eq76660
  have eq77337 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq77268
  have eq77406 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq77337 eq35276
    | exact resolve eq35276 eq77337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35276 eq77337
  have eq77480 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq77406
    | exact resolve eq77406 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77406
  have eq77494 : (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq77480
       have r₂ := eq71399
       grind)
    | exact resolve eq77480 eq71399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77480
  have eq77589 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq77494 eq35182
    | exact resolve eq35182 eq77494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35182 eq77494
  have eq78362 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq77589 eq20
    | exact resolve eq20 eq77589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq77589
  have eq78547 : False := by grind
  exact eq78547

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxx_y_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  clear eq24
  have eq50 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq14 X2 (M.op X2 x) X4 X5
       have i₂ := eq14 X2 x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq14 x x X4 X5
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq113
    | exact resolve eq113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq214 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq229 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq214 eq228
    | exact resolve eq228 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq232 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq14
    | exact resolve eq14 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq232 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq232
    | exact resolve eq232 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq235 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq214 eq233
    | exact resolve eq233 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq259 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq16
    | exact resolve eq16 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq391 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq411 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq229 eq391
    | exact resolve eq391 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq391
  have eq488 : ∀ X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq50 x x X2 X4 X5
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq50
    | exact resolve eq50 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq489 : ∀ X2 : G, (M.op x (M.op x y)) = (M.op X2 (M.op x (M.op x y))) := by
    intro X2
    first
    | (have i₁ := eq488 X2 x x
       have i₂ := eq411 x x
       grind)
    | exact superpose eq411 eq488
    | exact resolve eq488 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq502 : ∀ X0 : G, (M.op x (M.op x y)) ≠ (M.op x (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq489 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (M.op x (M.op x y))
       have r₂ := eq489 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq506 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq502 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502
  have eq515 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq54 x x X2 X3 X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq516 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq214 eq515
    | exact resolve eq515 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq517 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq516 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq516
    | exact resolve eq516 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq518 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq214 eq517
    | exact resolve eq517 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq553 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq55 X0 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq55
    | exact resolve eq55 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq554 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 (M.op x (M.op x y))) X0) := by
    intro X0
    first
    | (have i₁ := eq411 X0 X0
       have i₂ := eq506 X0
       grind)
    | exact superpose eq506 eq411
    | exact resolve eq411 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (k X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq214 eq553
    | exact resolve eq553 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq674 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq678 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq674 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq682 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq678 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq678 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq678 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq3351 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq506 eq682
    | (have j0 := eq682 (M.op x (M.op x y)) X0
       grind)
    | exact resolve eq682 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq3366 : ∀ X0 : G, (σ (M.op x (M.op x y))) ≠ (σ (M.op x (M.op x y))) ∨ (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq489 eq3351
    | (have j0 := eq3351 X0
       grind)
    | exact resolve eq3351 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq3351
  have eq3367 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq3366 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3366
  have eq3402 : ∀ X0 : G, (k (τ X0) (M.op x (M.op x y))) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq3367 eq259
    | exact resolve eq259 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq3407 : (M.op (σ x) (σ x)) = (σ (k x (M.op x (M.op x y)))) := by
    first
    | exact superpose eq3367 eq35
    | exact resolve eq35 eq3367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq3367
  have eq3432 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq506 eq3407
    | exact resolve eq3407 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3407
  have eq3476 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq3432
       grind)
    | exact superpose eq3432 eq16
    | exact resolve eq16 eq3432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3777 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq506 eq3402
    | exact resolve eq3402 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq3782 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq3402 eq558
    | exact resolve eq558 eq3402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq3783 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | exact superpose eq3402 eq554
    | exact resolve eq554 eq3402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq3402
  have eq4823 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq518 eq3782
    | exact resolve eq3782 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782
  have eq4854 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq4823
       have i₂ := eq3777 (M.op x sF0)
       grind)
    | exact superpose eq3777 eq4823
    | exact resolve eq4823 eq3777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4823
  have eq4874 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq518 eq4854
    | exact resolve eq4854 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4854
  have eq15696 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq115 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq15697 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq15696
    | exact resolve eq15696 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15696
  have eq15709 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq15697
       have r₂ := eq27
       grind)
    | exact resolve eq15697 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15697
  have eq15713 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq15709
    | exact resolve eq15709 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15709
  have eq15715 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq15713 eq3476
    | exact resolve eq3476 eq15713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476 eq15713
  have eq15737 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq15715
    | exact resolve eq15715 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15715
  have eq15738 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15737
  have eq15742 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3432
       have i₂ := eq15738
       grind)
    | exact superpose eq15738 eq3432
    | exact resolve eq3432 eq15738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432 eq15738
  have eq15762 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15742
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15742
    | exact resolve eq15742 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15742
  have eq15776 : (M.op (σ x) (σ x)) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15762 eq411
    | exact resolve eq411 eq15762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16443 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15776 eq15762
    | exact resolve eq15762 eq15776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15762 eq15776
  have eq16460 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16443
  have eq16477 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16460 eq235
    | exact resolve eq235 eq16460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq16460
  have eq16512 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16477
    | exact resolve eq16477 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16477
  have eq16513 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16512
  have eq16518 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16513 eq229
    | exact resolve eq229 eq16513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq16521 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16518
    | exact resolve eq16518 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16518
  have eq16704 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16521 eq518
    | exact resolve eq518 eq16521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq16715 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16521 eq4874
    | exact resolve eq4874 eq16521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4874 eq16521
  have eq16738 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16513 eq16715
    | exact resolve eq16715 eq16513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16715
  have eq16771 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq16738
  have eq16773 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq16771
    | exact resolve eq16771 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16771
  have eq17087 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16513 eq16704
    | exact resolve eq16704 eq16513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16513 eq16704
  have eq17115 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17087 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17087
  have eq17224 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16773 eq17115
    | exact resolve eq17115 eq16773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16773 eq17115
  have eq17262 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq17224 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17224
  have eq17458 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17262 y
       grind)
    | exact superpose eq17262 eq18
    | (have j1 := eq17262 y
       grind)
    | exact resolve eq18 eq17262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17262
  have eq17511 : x = (M.op x y) := by grind
  clear eq17458
  have eq17541 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq17511 eq20
    | exact resolve eq20 eq17511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq17587 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq17511 eq214
    | exact resolve eq214 eq17511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq17625 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq17587
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17587
    | exact resolve eq17587 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17587
  have eq17670 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq17541
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17541
    | exact resolve eq17541 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17541
  have eq17671 : x = (M.op x x) := by
    first
    | exact superpose eq17511 eq17625
    | exact resolve eq17625 eq17511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17625
  have eq17709 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq17670 eq26
    | exact resolve eq26 eq17670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq17857 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq17671
       grind)
    | exact superpose eq17671 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq17671
       grind)
    | exact resolve eq13 eq17671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17859 : (M.op x (M.op x y)) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq3783 x
       have i₂ := eq17671
       grind)
    | exact superpose eq17671 eq3783
    | exact resolve eq3783 eq17671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3783
  have eq17867 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq17857 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17857
  have eq17874 : (M.op x (M.op x y)) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq17859
       have i₂ := eq3777 x
       grind)
    | exact superpose eq3777 eq17859
    | exact resolve eq17859 eq3777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777 eq17859
  have eq17883 : (M.op x (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq17874
       have i₂ := eq17671
       grind)
    | exact superpose eq17671 eq17874
    | exact resolve eq17874 eq17671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17874
  have eq17892 : (M.op x x) = (τ x) := by
    first
    | exact superpose eq17511 eq17883
    | exact resolve eq17883 eq17511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17883
  have eq17898 : x = (τ x) := by
    first
    | (have i₁ := eq17892
       have i₂ := eq17671
       grind)
    | exact superpose eq17671 eq17892
    | exact resolve eq17892 eq17671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17892
  have eq17902 : x = (σ x) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq17898
       grind)
    | exact superpose eq17898 eq15
    | exact resolve eq15 eq17898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17898
  have eq17956 : x = (σ x) := by
    first
    | (have i₁ := eq17902
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17902
    | exact resolve eq17902 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17902
  have eq17969 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq17670 eq17956
    | exact resolve eq17956 eq17670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17670 eq17956
  have eq18244 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq17969 eq17709
    | exact resolve eq17709 eq17969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17709
  have eq18369 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (k X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq411 X0 X0
       have i₂ := eq17867 X0
       grind)
    | exact superpose eq17867 eq411
    | exact resolve eq411 eq17867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17867
  have eq18445 : ∀ X0 : G, (M.op x x) = (M.op (k X0 x) X0) := by
    intro X0
    first
    | exact superpose eq17511 eq18369
    | exact resolve eq18369 eq17511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18369
  have eq18501 : ∀ X0 : G, x = (M.op (k X0 x) X0) := by
    intro X0
    first
    | (have i₁ := eq18445 X0
       have i₂ := eq17671
       grind)
    | exact superpose eq17671 eq18445
    | exact resolve eq18445 eq17671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18445
  have eq18704 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq411 (k X0 x) X0
       have i₂ := eq18501 X0
       grind)
    | exact superpose eq18501 eq411
    | exact resolve eq411 eq18501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411 eq18501
  have eq18712 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq17511 eq18704
    | exact resolve eq18704 eq17511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17511 eq18704
  have eq18726 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq18712 X0
       have i₂ := eq17671
       grind)
    | exact superpose eq17671 eq18712
    | exact resolve eq18712 eq17671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17671 eq18712
  have eq18763 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18244 eq18726
    | exact resolve eq18726 eq18244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18244 eq18726
  have eq18867 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq18763 eq27
    | exact resolve eq27 eq18763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq18763
  have eq18882 : False := by grind
  exact eq18882

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pyx_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
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
  clear eq44
  have eq55 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq81 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq77 sF2
       grind)
    | exact superpose eq77 eq50
    | exact resolve eq50 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq82 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq81
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq81
    | exact resolve eq81 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq91 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq77 sF3
       grind)
    | exact superpose eq77 eq75
    | exact resolve eq75 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq92 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq91
       have i₂ := eq77 y
       grind)
    | exact superpose eq77 eq91
    | exact resolve eq91 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
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
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq100
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq100
    | exact resolve eq100 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq117 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq229 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq56 X0 (M.op X0 x)
       have i₂ := eq56 X0 x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq77 (τ X0)
       grind)
    | exact superpose eq77 eq35
    | exact resolve eq35 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq274 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq263 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq263
    | exact resolve eq263 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq276 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq274 X0
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq274
    | exact resolve eq274 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq274
  have eq405 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq232 eq229
    | exact resolve eq229 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq406 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq232 eq234
    | exact resolve eq234 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq544 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq55 x x X2 X3 X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq545 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq232 eq544
    | exact resolve eq544 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq546 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq545 x x X5
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq545
    | exact resolve eq545 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq545
  have eq547 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq232 eq546
    | exact resolve eq546 eq232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232 eq546
  have eq784 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq276 X0
       grind)
    | exact superpose eq276 eq16
    | exact resolve eq16 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq1017 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq406 (τ X0) (τ X0)
       have i₂ := eq784 X0
       grind)
    | exact superpose eq784 eq406
    | exact resolve eq406 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1493 : (M.op x (M.op x y)) = (M.op (τ (M.op x (M.op x y))) (τ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq547 eq1017
    | exact resolve eq1017 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1539 : (M.op x (M.op x y)) = (τ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq1493
       have i₂ := eq784 (M.op x sF0)
       grind)
    | exact superpose eq784 eq1493
    | exact resolve eq1493 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784 eq1493
  have eq1548 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq547 eq1539
    | exact resolve eq1539 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq1539
  have eq1551 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq1548 eq15
    | exact resolve eq15 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq12975 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq12976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq27 eq12975
    | exact resolve eq12975 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12975
  have eq12987 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq12976
       have r₂ := eq28
       grind)
    | exact resolve eq12976 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12976
  have eq12991 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq12987 eq117
    | exact resolve eq117 eq12987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq12987
  have eq13025 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
    first
    | exact superpose eq30 eq12991
    | exact resolve eq12991 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12991
  have eq13026 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13025
  have eq13045 : (M.op y y) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq406 y y
       have i₂ := eq13026
       grind)
    | exact superpose eq13026 eq406
    | exact resolve eq406 eq13026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq13241 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13026
       have i₂ := eq13045
       grind)
    | exact superpose eq13045 eq13026
    | exact resolve eq13026 eq13045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13026 eq13045
  have eq13253 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq13241
  have eq13275 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq13253 eq405
    | exact resolve eq405 eq13253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13288 : y = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13253 eq1551
    | exact resolve eq1551 eq13253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1551 eq13253
  have eq13298 : (σ x) = (σ y) ∨ y = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13288
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq13288
    | exact resolve eq13288 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13288
  have eq13304 : y = (τ (σ x)) ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq13298 eq30
    | exact resolve eq30 eq13298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13298
  have eq13414 : x = y ∨ y = (σ y) ∨ x = y := by
    first
    | exact superpose eq29 eq13304
    | exact resolve eq13304 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13304
  have eq13415 : y = (σ y) ∨ x = y := by grind
  clear eq13414
  have eq13565 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ x = y := by
    first
    | exact superpose eq13415 eq27
    | exact resolve eq27 eq13415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14281 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13275 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13275
    | (have j0 := eq13275 x
       grind)
    | exact resolve eq13275 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13275
  have eq14477 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq14281 eq30
    | exact resolve eq30 eq14281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14281
  have eq14602 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq14477
    | exact resolve eq14477 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14477
  have eq14603 : y = (M.op x y) ∨ x = y := by grind
  clear eq14602
  have eq14618 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14603 eq21
    | exact resolve eq21 eq14603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14667 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14603 eq405
    | exact resolve eq405 eq14603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq14700 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq14667 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14667
    | (have j0 := eq14667 X0
       grind)
    | exact resolve eq14667 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14667
  have eq14749 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14618
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq14618
    | exact resolve eq14618 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14618
  have eq14834 : y = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq14749 eq13415
    | exact resolve eq13415 eq14749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13415 eq14749
  have eq14843 : y = (σ (M.op x y)) ∨ x = y := by grind
  clear eq14834
  have eq15577 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq14603 eq14700
    | exact resolve eq14700 eq14603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14603 eq14700
  have eq15630 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq15577 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15577
  have eq15893 : y = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq13565
       have i₂ := eq15630 sF2
       grind)
    | exact superpose eq15630 eq13565
    | exact resolve eq13565 eq15630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13565 eq15630
  have eq15896 : y = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq15893
  have eq15938 : y ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq15896 eq28
    | exact resolve eq28 eq15896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15896
  have eq15940 : x = y := by
    first
    | (have r₁ := eq15938
       have r₂ := eq14843
       grind)
    | exact resolve eq15938 eq14843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14843 eq15938
  have eq15942 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15940
       grind)
    | exact superpose eq15940 eq19
    | exact resolve eq19 eq15940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15943 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq15940
       grind)
    | exact superpose eq15940 eq25
    | exact resolve eq25 eq15940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq15940
  have eq16045 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15943
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15943
    | exact resolve eq15943 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq15943
  have eq16063 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16045 eq27
    | exact resolve eq27 eq16045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16045
  have eq16263 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq16063 eq82
    | exact resolve eq82 eq16063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq16063
  have eq16293 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq16263
       have i₂ := eq15942
       grind)
    | exact superpose eq15942 eq16263
    | exact resolve eq16263 eq15942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15942 eq16263
  have eq16305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16293 eq15
    | exact resolve eq15 eq16293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16293
  have eq16351 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16305
    | exact resolve eq16305 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq16305
  have eq16359 : False := by grind
  exact eq16359

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxy_pxx_pyx_Equation4430 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq57 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq94 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq94
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq107
    | exact resolve eq107 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq216 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq58 X0 (M.op X0 x)
       have i₂ := eq58 X0 x
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq58 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq58
    | (have j0 := eq58 x y
       grind)
    | exact resolve eq58 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq59 x x
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq59
    | exact resolve eq59 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq234 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq219 eq233
    | exact resolve eq233 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq237 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq234 eq14
    | exact resolve eq14 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq238 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq237 x x
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq237
    | exact resolve eq237 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq240 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq219 eq238
    | exact resolve eq238 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq406 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq58 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq58
    | exact resolve eq58 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq219 eq406
    | exact resolve eq406 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq412 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq219 eq216
    | exact resolve eq216 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq562 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq57 x x X2 X3 X5
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq57
    | exact resolve eq57 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq563 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq219 eq562
    | exact resolve eq562 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq564 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq563 x x X5
       have i₂ := eq58 x x
       grind)
    | exact superpose eq58 eq563
    | exact resolve eq563 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq565 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq219 eq564
    | exact resolve eq564 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq1055 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq565 eq410
    | exact resolve eq410 eq565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq1085 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq1055
       have i₂ := eq45 (M.op x sF0)
       grind)
    | exact superpose eq45 eq1055
    | exact resolve eq1055 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq1055
  have eq1102 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq412 eq1085
    | exact resolve eq1085 eq412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq1085
  have eq1119 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq1102 eq16
    | exact resolve eq16 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq12378 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq12377
    | exact resolve eq12377 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12377
  have eq12389 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq12378
       have r₂ := eq28
       grind)
    | exact resolve eq12378 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12378
  have eq12521 : (M.op (M.op x y) y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq12389 eq58
    | exact resolve eq58 eq12389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12527 : (M.op x (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq219 eq12521
    | exact resolve eq12521 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12521
  have eq14285 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq12527 eq12389
    | exact resolve eq12389 eq12527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12389 eq12527
  have eq14295 : (σ x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq14285
  have eq14304 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14295 eq240
    | exact resolve eq240 eq14295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14314 : (σ x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq14295 eq1119
    | exact resolve eq1119 eq14295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119 eq14295
  have eq14347 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq14314
    | exact resolve eq14314 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14314
  have eq14348 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq14304
    | exact resolve eq14304 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14304
  have eq14357 : (M.op (M.op x y) y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq58 y x
       have i₂ := eq14347
       grind)
    | exact superpose eq14347 eq58
    | exact resolve eq58 eq14347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14363 : (M.op y x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq219 eq14357
    | exact resolve eq14357 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14357
  have eq14372 : (M.op (M.op x y) y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq58 y x
       have i₂ := eq14348
       grind)
    | exact superpose eq14348 eq58
    | exact resolve eq58 eq14348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq14378 : (M.op y x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq219 eq14372
    | exact resolve eq14372 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq14372
  have eq14606 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14347
       have i₂ := eq14363
       grind)
    | exact superpose eq14363 eq14347
    | exact resolve eq14347 eq14363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14347 eq14363
  have eq14616 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by grind
  clear eq14606
  have eq14639 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq14616 eq1102
    | exact resolve eq1102 eq14616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102 eq14616
  have eq14675 : x = (σ x) ∨ (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq14639
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14639
    | exact resolve eq14639 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14639
  have eq14676 : (σ x) = (σ y) ∨ x = (σ x) ∨ x = y := by grind
  clear eq14675
  have eq14680 : y = (τ (σ x)) ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq14676 eq30
    | exact resolve eq30 eq14676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14802 : x = y ∨ x = (σ x) ∨ x = y := by
    first
    | exact superpose eq29 eq14680
    | exact resolve eq14680 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14680
  have eq14803 : x = (σ x) ∨ x = y := by grind
  clear eq14802
  have eq14823 : (M.op (σ x) (σ y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | exact superpose eq14803 eq27
    | exact resolve eq27 eq14803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2052671 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq14348
       have i₂ := eq14378
       grind)
    | exact superpose eq14378 eq14348
    | exact resolve eq14348 eq14378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14348 eq14378
  have eq2052691 : x = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2052671
  have eq2052721 : x = (M.op x (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2052691 eq240
    | exact resolve eq240 eq2052691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq2052691
  have eq2052912 : x = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2052721 eq14823
    | exact resolve eq14823 eq2052721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052721
  have eq2052922 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq2052912
  have eq2052945 : x ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op (σ x) (σ y)) := by grind
  clear eq2052922
  have eq2052949 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2052945
       have r₂ := eq14676
       grind)
    | exact resolve eq2052945 eq14676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14676 eq2052945
  have eq2052952 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2052949 eq30
    | exact resolve eq30 eq2052949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2052949
  have eq2053888 : x = y ∨ x = y ∨ x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq2052952
    | exact resolve eq2052952 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2052952
  have eq2053889 : x = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq2053888
  have eq2053993 : x ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2053889 eq28
    | exact resolve eq28 eq2053889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2053995 : (M.op x (M.op x y)) = (M.op x (σ y)) ∨ x = y := by
    first
    | exact superpose eq2053889 eq234
    | exact resolve eq234 eq2053889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq2054012 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2053995 eq14823
    | exact resolve eq14823 eq2053995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14823 eq2053995
  have eq2054025 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq2054012
  have eq2054056 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2054025 eq565
    | exact resolve eq565 eq2054025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq2054025
  have eq2055563 : ∀ X0 : G, x = (M.op x X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq2053889 eq2054056
    | exact resolve eq2054056 eq2053889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053889 eq2054056
  have eq2055664 : ∀ X0 : G, x = (M.op x X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2055563 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055563
  have eq2059026 : x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2055664 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2055664
    | (have j0 := eq2055664 y
       grind)
    | exact resolve eq2055664 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2055664
  have eq2059885 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq2059026 eq21
    | exact resolve eq21 eq2059026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059026
  have eq2061553 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq2059885
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2059885
    | exact resolve eq2059885 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2059885
  have eq2063855 : x = (σ (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2061553 eq14803
    | exact resolve eq14803 eq2061553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14803 eq2061553
  have eq2067657 : x = (σ (M.op x y)) ∨ x = y := by grind
  clear eq2063855
  have eq2067811 : x = y := by
    first
    | (have r₁ := eq2067657
       have r₂ := eq2053993
       grind)
    | exact resolve eq2067657 eq2053993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2053993 eq2067657
  have eq2068054 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2067811
       grind)
    | exact superpose eq2067811 eq19
    | exact resolve eq19 eq2067811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2068055 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2067811
       grind)
    | exact superpose eq2067811 eq25
    | exact resolve eq25 eq2067811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2067811
  have eq2069241 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2068055
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2068055
    | exact resolve eq2068055 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2068055
  have eq2071248 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2069241 eq27
    | exact resolve eq27 eq2069241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2069241
  have eq2072723 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2071248 eq72
    | exact resolve eq72 eq2071248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq2071248
  have eq2073010 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2072723
       have i₂ := eq2068054
       grind)
    | exact superpose eq2068054 eq2072723
    | exact resolve eq2072723 eq2068054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2068054 eq2072723
  have eq2073085 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2073010 eq15
    | exact resolve eq15 eq2073010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2073010
  have eq2074012 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2073085
    | exact resolve eq2073085 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2073085
  have eq2074255 : False := by grind
  exact eq2074255

/-- `Equation4438`: `x ◇ (y ◇ x) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_y_pyx_Equation4438 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4438 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4438.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X0) := by
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq44
    | (have j0 := eq44 (M.op x y)
       grind)
    | exact resolve eq44 eq20
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq47
    | (have j0 := eq47 (M.op x y)
       grind)
    | exact resolve eq47 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq131 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  have eq174 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) (M.op X2 X0)) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 X0) X0 X3
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X2) X3 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) x) := by
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
  have eq181 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq36 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq36
    | exact resolve eq36 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ y) = (k (σ y) (σ (M.op y y))) := by
    first
    | (have i₁ := eq184
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq184
    | exact resolve eq184 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq198 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op (M.op x y) x) x) := by
    intro X0
    first
    | (have i₁ := eq16 x X0 (M.op x x)
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) x) := by
    first
    | (have i₁ := eq198 x
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq198
    | exact resolve eq198 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq203 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X1) (σ x)) := by
    intro X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | (have i₁ := eq90 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq90
    | exact resolve eq90 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq241 : x = (k x (τ (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq29 eq230
    | exact resolve eq230 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq248 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq107 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq107
    | exact resolve eq107 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq259 : y = (k y (τ (M.op (σ y) (σ y)))) := by
    first
    | exact superpose eq31 eq248
    | exact resolve eq248 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq438 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq746 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 y X0 x
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq182
    | (have j0 := eq182 (σ y) X0 (σ x)
       grind)
    | exact resolve eq182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k y x) := by
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
  have eq849 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq863 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq865 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq174
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq174 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 (k X0 X0)
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op X0 X0) X0)
       have r₂ := eq11 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq914 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq866 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq915 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq865 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq947 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op y X1) y) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq810 x
       grind)
    | (have i₁ := eq16 y x x
       have i₂ := eq810 x
       grind)
    | exact superpose eq810 eq16
    | (have j0 := eq16 y x X1
       grind)
    | exact resolve eq16 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) (σ y)) := by
    intro X1
    first
    | exact superpose eq812 eq16
    | (have j0 := eq16 (σ y) (σ x) X1
       grind)
    | exact resolve eq16 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq861
       grind)
    | exact superpose eq861 eq39
    | exact resolve eq39 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1420 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1419
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1419
    | exact resolve eq1419 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq1422 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1420
    | exact resolve eq1420 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq1680 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1422 eq863
    | exact resolve eq863 eq1422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1687 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq1680
       have r₂ := eq27
       grind)
    | exact resolve eq1680 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq1730 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1687 eq259
    | exact resolve eq259 eq1687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1687
  have eq1758 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq1730
    | exact resolve eq1730 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1767 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1758
       have r₂ := eq13 y x
       grind)
    | exact resolve eq1758 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758
  have eq1771 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq861
       have i₂ := eq1767
       grind)
    | exact superpose eq1767 eq861
    | exact resolve eq861 eq1767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1773 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1767
       grind)
    | exact superpose eq1767 eq39
    | exact resolve eq39 eq1767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq1775 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1771
  have eq1779 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1773
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1773
    | exact resolve eq1773 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1773
  have eq1785 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1779 eq1422
    | exact resolve eq1422 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1786 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1779 eq863
    | exact resolve eq863 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1791 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1786
  have eq1792 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1785
  have eq1803 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq947 y
       have i₂ := eq1775
       grind)
    | exact superpose eq1775 eq947
    | exact resolve eq947 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1804 : (M.op y (M.op x y)) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq810 y
       have i₂ := eq1775
       grind)
    | exact superpose eq1775 eq810
    | exact resolve eq810 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1806 : ∀ X0 : G, x ≠ X0 ∨ y = (k y X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq1775
       grind)
    | exact superpose eq1775 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1775
       grind)
    | exact resolve eq13 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1807 : x = (k y y) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1775
       grind)
    | exact superpose eq1775 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1816 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq746 y y X0
       have i₂ := eq1775
       grind)
    | exact superpose eq1775 eq746
    | exact resolve eq746 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1818 : x = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1807
  have eq1821 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1816 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1816
    | (have j0 := eq1816 X0
       grind)
    | exact resolve eq1816 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1829 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1803
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1803
    | exact resolve eq1803 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803
  have eq1833 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1821 x
       have i₂ := eq947 x
       grind)
    | exact superpose eq947 eq1821
    | exact resolve eq1821 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq1839 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1829 eq1833
    | exact resolve eq1833 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1841 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1791
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq1791
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq1791 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1843 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1791 eq967
    | exact resolve eq967 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1844 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1791 eq812
    | exact resolve eq812 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1846 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1791 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1791
       grind)
    | exact resolve eq13 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1847 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1791 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1856 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1791 eq746
    | exact resolve eq746 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1858 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1847
  have eq1859 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1841
  have eq1861 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1856
    | (have j0 := eq1856 X0
       grind)
    | exact resolve eq1856 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1856
  have eq1869 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1843
    | exact resolve eq1843 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1843
  have eq1871 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1858 eq1859
    | exact resolve eq1859 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1859
  have eq1873 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq967 eq1861
    | exact resolve eq1861 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1861
  have eq1879 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1869 eq1873
    | exact resolve eq1873 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1873
  have eq1883 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq947 y
       have i₂ := eq1792
       grind)
    | exact superpose eq1792 eq947
    | exact resolve eq947 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq746 y y X0
       have i₂ := eq1792
       grind)
    | exact superpose eq1792 eq746
    | exact resolve eq746 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1901 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1896 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1896
    | (have j0 := eq1896 X0
       grind)
    | exact resolve eq1896 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896
  have eq1909 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1883
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1883
    | exact resolve eq1883 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883
  have eq1913 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1901 x
       have i₂ := eq947 x
       grind)
    | exact superpose eq947 eq1901
    | exact resolve eq1901 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1901
  have eq1919 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1909 eq1913
    | exact resolve eq1913 eq1909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909 eq1913
  have eq1924 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1829 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1932 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1829 eq182
    | exact resolve eq182 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1935 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1924
  have eq1941 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq1935
       have r₂ := eq13 (M.op x y) y
       grind)
    | exact resolve eq1935 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935
  have eq1951 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1839 eq12
    | (have j0 := eq12 y (M.op x y)
       grind)
    | (have r₁ := eq12 y (M.op x y)
       have r₂ := eq1839
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1839
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1839
       grind)
    | exact resolve eq12 eq1839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1839
  have eq1961 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1951
  have eq1973 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1869 eq177
    | exact resolve eq177 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1982 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq967 eq1973
    | exact resolve eq1973 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973
  have eq1989 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1844 eq1982
    | exact resolve eq1982 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982
  have eq1994 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1879 eq1989
    | exact resolve eq1989 eq1879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1879 eq1989
  have eq2061 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1941 eq40
    | exact resolve eq40 eq1941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941
  have eq2063 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2061
    | exact resolve eq2061 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2061
  have eq2188 : (M.op (M.op x y) x) = (M.op x (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 y
       have i₂ := eq1804
       grind)
    | exact superpose eq1804 eq180
    | exact resolve eq180 eq1804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804
  have eq2206 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1829 eq2188
    | exact resolve eq2188 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829 eq2188
  have eq2290 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2206 eq182
    | exact resolve eq182 eq2206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2295 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1932 eq2290
    | exact resolve eq2290 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932 eq2290
  have eq2815 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1818
       grind)
    | exact superpose eq1818 eq40
    | exact resolve eq40 eq1818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq2821 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2815
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2815
    | exact resolve eq2815 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815
  have eq2823 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2821
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2821
    | exact resolve eq2821 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821
  have eq3025 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1858 eq115
    | exact resolve eq115 eq1858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3035 : x = (k y y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq3025
    | exact resolve eq3025 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3025
  have eq3917 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2823 eq869
    | (have j0 := eq869 (σ y) (σ y) x
       grind)
    | exact resolve eq869 eq2823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3997 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3917 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3917
  have eq4020 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq812 eq3997
    | (have j0 := eq3997 (σ x)
       grind)
    | exact resolve eq3997 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3997
  have eq4035 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq4020
    | exact resolve eq4020 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4020
  have eq4242 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1871 eq115
    | exact resolve eq115 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871
  have eq4258 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq4242
    | exact resolve eq4242 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4242
  have eq4280 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1961 eq36
    | exact resolve eq36 eq1961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq4288 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4280
    | exact resolve eq4280 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4280
  have eq4348 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq4258 eq181
    | exact resolve eq181 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4374 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq4258 eq4348
    | exact resolve eq4348 eq4258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4258 eq4348
  have eq4409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4288 eq902
    | (have j0 := eq902 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq902 (σ (M.op x y)) (σ y)
       have r₂ := eq4288
       grind)
    | exact resolve eq902 eq4288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4410 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4409
  have eq4411 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1775 eq4410
    | exact resolve eq4410 eq1775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1775 eq4410
  have eq4412 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4411
  have eq4555 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4412 eq1791
    | exact resolve eq1791 eq4412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4558 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4412 eq967
    | exact resolve eq967 eq4412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4559 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4412 eq812
    | exact resolve eq812 eq4412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4560 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4412 eq174
    | exact resolve eq174 eq4412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4580 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq4555
  have eq4596 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4559 eq4558
    | exact resolve eq4558 eq4559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4558 eq4559
  have eq4686 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4560 eq4288
    | exact resolve eq4288 eq4560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4288 eq4560
  have eq4694 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq4686
  have eq4701 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1792 eq4694
    | exact resolve eq4694 eq1792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4694
  have eq4702 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq4701
  have eq5130 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq4702 eq812
    | exact resolve eq812 eq4702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5132 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq4702 eq16
    | exact resolve eq16 eq4702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6198 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4580 eq812
    | exact resolve eq812 eq4580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6200 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4580 eq16
    | exact resolve eq16 eq4580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4580
  have eq6231 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5132 eq6200
    | (have j0 := eq6200 X0
       have j1 := eq5132 X0
       grind)
    | exact resolve eq6200 eq5132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5132 eq6200
  have eq6233 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5130 eq6198
    | exact resolve eq6198 eq5130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5130 eq6198
  have eq6244 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1844 eq6233
    | exact resolve eq6233 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6233
  have eq6252 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1994 eq6244
    | exact resolve eq6244 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6244
  have eq6267 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6252 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq6252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6252
  have eq6286 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq6267
  have eq6301 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2063 eq6286
    | exact resolve eq6286 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6286
  have eq6313 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6301
       have r₂ := eq27
       grind)
    | exact resolve eq6301 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6301
  have eq6339 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ (M.op x y)) (M.op X1 (σ (M.op x y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6313 eq179
    | exact resolve eq179 eq6313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq6356 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (M.op X1 (σ (M.op x y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq812 eq6339
    | (have j0 := eq6339 (σ x) X1
       grind)
    | exact resolve eq6339 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6339
  have eq6368 : ∀ X1 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ (M.op x y)) (M.op X1 (σ (M.op x y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq1844 eq6356
    | exact resolve eq6356 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6356
  have eq6376 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (M.op X1 (σ (M.op x y)))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq1994 eq6368
    | exact resolve eq6368 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994 eq6368
  have eq6379 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6231 eq6376
    | exact resolve eq6376 eq6231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6231 eq6376
  have eq6381 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6313 eq6379
    | exact resolve eq6379 eq6313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6313 eq6379
  have eq6383 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1791 eq6381
    | exact resolve eq6381 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6381
  have eq6384 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq6383
  have eq7807 : (σ (M.op x y)) ≠ (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4596
  have eq7811 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4702 eq7807
    | exact resolve eq7807 eq4702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7807
  have eq7900 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4412 eq7811
    | exact resolve eq7811 eq4412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4412
  have eq7901 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1791 eq7811
    | exact resolve eq7811 eq1791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1791 eq7811
  have eq7906 : (σ x) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7901
  have eq7907 : (σ (M.op x y)) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7900
  have eq7909 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7906
       have r₂ := eq6384
       grind)
    | exact resolve eq7906 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7906
  have eq7910 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7907
       have r₂ := eq4702
       grind)
    | exact resolve eq7907 eq4702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4702 eq7907
  have eq7911 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6384 eq7909
    | exact resolve eq7909 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7909
  have eq7914 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7910 eq812
    | exact resolve eq812 eq7910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7916 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7910 eq16
    | exact resolve eq16 eq7910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7949 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6384 eq7914
    | exact resolve eq7914 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7952 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1844 eq7914
    | exact resolve eq7914 eq1844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1844
  have eq7959 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7914 eq1869
    | exact resolve eq1869 eq7914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869 eq7914
  have eq7986 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7959
  have eq7991 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7952
  have eq7994 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7949
  have eq7998 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6384 eq7986
    | exact resolve eq7986 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7986
  have eq8002 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6384 eq7991
    | exact resolve eq7991 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7991
  have eq8005 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7998 eq8002
    | exact resolve eq8002 eq7998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8002
  have eq8007 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7911 eq181
    | exact resolve eq181 eq7911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7911
  have eq8038 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7998 eq8007
    | exact resolve eq8007 eq7998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7998 eq8007
  have eq8061 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8038 eq4374
    | exact resolve eq4374 eq8038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4374 eq8038
  have eq8089 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq8061
  have eq8151 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8005 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq8005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8005
  have eq8173 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8151
  have eq8247 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq8089
       grind)
    | exact superpose eq8089 eq40
    | exact resolve eq40 eq8089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8089
  have eq8258 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8247
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8247
    | exact resolve eq8247 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8247
  have eq8261 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8258
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8258
    | exact resolve eq8258 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8258
  have eq8263 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6384 eq8261
    | exact resolve eq8261 eq6384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6384 eq8261
  have eq8294 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8263 eq8173
    | exact resolve eq8173 eq8263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173 eq8263
  have eq8308 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8294
  have eq8314 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8308 eq27
    | exact resolve eq27 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8341 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq8874 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7994 eq7916
    | exact resolve eq7916 eq7994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7916
  have eq8876 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7994 eq12
    | (have j0 := eq12 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq7994
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7994
       grind)
    | exact resolve eq12 eq7994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7994
  have eq8896 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8874
  have eq8921 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8876
       have r₂ := eq8341
       grind)
    | exact resolve eq8876 eq8341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8876
  have eq8923 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8896
       have r₂ := eq8341
       grind)
    | exact resolve eq8896 eq8341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8896
  have eq8934 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2063 eq8921
    | exact resolve eq8921 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063 eq8921
  have eq8941 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8934
       have r₂ := eq8314
       grind)
    | exact resolve eq8934 eq8314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8934
  have eq10618 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4035 eq967
    | exact resolve eq967 eq4035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4035
  have eq10678 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8308 eq10618
    | exact resolve eq10618 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10618
  have eq10679 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10678
  have eq10711 : y = (k y (τ (σ y))) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10679 eq259
    | exact resolve eq259 eq10679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10722 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10679 eq174
    | exact resolve eq174 eq10679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq10679
  have eq10771 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2823 eq10722
    | exact resolve eq10722 eq2823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823 eq10722
  have eq10777 : y = (k y y) ∨ x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq10711
    | exact resolve eq10711 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10711
  have eq10791 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq10771
       have r₂ := eq8341
       grind)
    | exact resolve eq10771 eq8341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8341 eq10771
  have eq10795 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1806 y
       grind)
    | (have r₁ := eq10777
       have r₂ := eq1806 y
       grind)
    | (have r₁ := eq10777
       have r₂ := eq1806 (M.op x y)
       grind)
    | exact resolve eq10777 eq1806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1806 eq10777
  have eq10805 : x = (k x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10791 eq10795
    | exact resolve eq10795 eq10791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10791 eq10795
  have eq10820 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq10805
       grind)
    | exact superpose eq10805 eq39
    | exact resolve eq39 eq10805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10825 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq902 x x
       have i₂ := eq10805
       grind)
    | exact superpose eq10805 eq902
    | (have j0 := eq902 x x
       grind)
    | (have r₁ := eq902 x x
       have r₂ := eq10805
       grind)
    | exact resolve eq902 eq10805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10805
  have eq10826 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10825
  have eq10827 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10826
  have eq10833 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10820
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10820
    | exact resolve eq10820 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10820
  have eq10838 : (M.op (M.op x y) x) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq10827
       grind)
    | exact superpose eq10827 eq180
    | exact resolve eq180 eq10827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10874 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10827 eq10838
    | exact resolve eq10838 eq10827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10827 eq10838
  have eq10902 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10833 eq902
    | (have j0 := eq902 (σ x) (σ x)
       grind)
    | (have r₁ := eq902 (σ x) (σ x)
       have r₂ := eq10833
       grind)
    | exact resolve eq902 eq10833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10833
  have eq10903 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10902
  have eq10904 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10903
  have eq10917 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10874 eq2295
    | exact resolve eq2295 eq10874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq10947 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10917
  have eq10967 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10874 eq10947
    | exact resolve eq10947 eq10874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10874 eq10947
  have eq10993 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10904 eq181
    | exact resolve eq181 eq10904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq11032 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8308 eq10993
    | exact resolve eq10993 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10993
  have eq11046 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10904 eq11032
    | exact resolve eq11032 eq10904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10904 eq11032
  have eq11074 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10967 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq10967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11096 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11074
  have eq11149 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11046 eq967
    | exact resolve eq967 eq11046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11046
  have eq11201 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11149
    | exact resolve eq11149 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11149
  have eq11219 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8308 eq11201
    | exact resolve eq11201 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8308 eq11201
  have eq11480 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11219 eq8923
    | exact resolve eq8923 eq11219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8923
  have eq11481 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11219 eq8941
    | (have r₁ := eq8941
       have r₂ := eq11219
       grind)
    | exact resolve eq8941 eq11219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8941 eq11219
  have eq11507 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11481
  have eq11508 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11507
  have eq11509 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq11480
  have eq11534 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7910 eq11509
    | exact resolve eq11509 eq7910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7910 eq11509
  have eq11546 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11508 eq11534
    | exact resolve eq11534 eq11508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11508 eq11534
  have eq11553 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11546
       have r₂ := eq8314
       grind)
    | exact resolve eq11546 eq8314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8314 eq11546
  have eq11557 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11553 eq27
    | exact resolve eq27 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11559 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11553 eq849
    | (have r₁ := eq849
       have r₂ := eq11553
       grind)
    | exact resolve eq849 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11561 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq11559
  have eq12232 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11561 eq1422
    | exact resolve eq1422 eq11561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1422
  have eq12243 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12232
  have eq12255 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12243
       have r₂ := eq11557
       grind)
    | exact resolve eq12243 eq11557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12243
  have eq12377 : y = (k y (τ (σ x))) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12255 eq259
    | exact resolve eq259 eq12255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12255
  have eq12447 : y = (k y x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq12377
    | exact resolve eq12377 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12377
  have eq12464 : y = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq12447
       have r₂ := eq13 y x
       grind)
    | exact resolve eq12447 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12447
  have eq12483 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq861
       have i₂ := eq12464
       grind)
    | exact superpose eq12464 eq861
    | exact resolve eq861 eq12464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12485 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq12464
       grind)
    | exact superpose eq12464 eq39
    | exact resolve eq39 eq12464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12464
  have eq12488 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12483
  have eq12493 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12485
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq12485
    | exact resolve eq12485 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12485
  have eq12498 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq947 y
       have i₂ := eq12488
       grind)
    | exact superpose eq12488 eq947
    | exact resolve eq947 eq12488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12499 : (M.op y (M.op x y)) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq810 y
       have i₂ := eq12488
       grind)
    | exact superpose eq12488 eq810
    | exact resolve eq810 eq12488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12514 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq746 y y X0
       have i₂ := eq12488
       grind)
    | exact superpose eq12488 eq746
    | exact resolve eq746 eq12488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq12531 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12514 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12514
    | (have j0 := eq12514 X0
       grind)
    | exact resolve eq12514 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12514
  have eq12542 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12498
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12498
    | exact resolve eq12498 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12498
  have eq12550 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12531 x
       have i₂ := eq947 x
       grind)
    | exact superpose eq947 eq12531
    | exact resolve eq12531 eq947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12531
  have eq12561 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12542 eq12550
    | exact resolve eq12550 eq12542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12550
  have eq12571 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12493 eq11561
    | exact resolve eq11561 eq12493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11561
  have eq12576 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12571
  have eq12590 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12542 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq12542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12601 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12542 eq182
    | exact resolve eq182 eq12542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq12612 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq12590
  have eq12624 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq12612
       have r₂ := eq13 (M.op x y) y
       grind)
    | exact resolve eq12612 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12612
  have eq12638 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12561 eq12
    | (have j0 := eq12 y (M.op x y)
       grind)
    | (have r₁ := eq12 y (M.op x y)
       have r₂ := eq12561
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq12561
       grind)
    | exact resolve eq12 eq12561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12561
  have eq12658 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq12638
  have eq12666 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12624 eq40
    | exact resolve eq40 eq12624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12670 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq12666
    | exact resolve eq12666 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12666
  have eq12770 : (k x y) = (M.op y (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq12499
       grind)
    | exact superpose eq12499 eq11
    | (have j0 := eq11 (M.op x y) y
       grind)
    | exact resolve eq11 eq12499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12499
  have eq12801 : (M.op x y) = (k x y) ∨ y = (M.op y (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12542 eq12770
    | exact resolve eq12770 eq12542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12770
  have eq12813 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12542 eq12801
    | exact resolve eq12801 eq12542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12542 eq12801
  have eq12814 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq12813
  have eq12915 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12576 eq967
    | exact resolve eq967 eq12576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12973 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq12915
    | exact resolve eq12915 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12915
  have eq12993 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11553 eq12973
    | exact resolve eq12973 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12973
  have eq13098 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12993 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq12993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13120 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13098
  have eq13149 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13120
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13120 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13120
  have eq13201 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13149 eq152
    | exact resolve eq152 eq13149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq13149
  have eq13209 : x = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq13201
    | exact resolve eq13201 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13201
  have eq13772 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12658 eq36
    | exact resolve eq36 eq12658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13780 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq13772
    | exact resolve eq13772 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13772
  have eq13784 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13209
       have i₂ := eq12814
       grind)
    | exact superpose eq12814 eq13209
    | exact resolve eq13209 eq12814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13209
  have eq13787 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq12814
       grind)
    | exact superpose eq12814 eq40
    | exact resolve eq40 eq12814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12814
  have eq13793 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq13784
  have eq13797 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13787
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq13787
    | exact resolve eq13787 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13787
  have eq13800 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq13797
    | exact resolve eq13797 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13797
  have eq13802 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13793 eq13800
    | exact resolve eq13800 eq13793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13800
  have eq13810 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq13793
       grind)
    | exact superpose eq13793 eq180
    | exact resolve eq180 eq13793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13858 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13810
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13810
    | exact resolve eq13810 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13810
  have eq14132 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13780 eq902
    | (have j0 := eq902 (σ (M.op x y)) (σ y)
       grind)
    | (have r₁ := eq902 (σ (M.op x y)) (σ y)
       have r₂ := eq13780
       grind)
    | exact resolve eq902 eq13780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13780
  have eq14133 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq14132
  have eq14138 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12488 eq14133
    | exact resolve eq14133 eq12488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12488 eq14133
  have eq14139 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq14138
  have eq14225 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14139 eq12576
    | exact resolve eq12576 eq14139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12576 eq14139
  have eq14256 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq14225
  have eq14289 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq14256
       have r₂ := eq11557
       grind)
    | exact resolve eq14256 eq11557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14256
  have eq14329 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14289 eq812
    | exact resolve eq812 eq14289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14335 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq14289 eq177
    | exact resolve eq177 eq14289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq14289
  have eq14362 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11553 eq14329
    | exact resolve eq14329 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14329
  have eq14372 : (σ x) = (M.op (σ y) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12993 eq14362
    | exact resolve eq14362 eq12993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12993 eq14362
  have eq14469 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14372 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq14372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14472 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) X1) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq14372 eq175
    | exact resolve eq175 eq14372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq14372
  have eq14490 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq14469
  have eq14517 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) X1) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X1
    first
    | exact superpose eq203 eq14472
    | (have j0 := eq14472 (σ y) X1
       grind)
    | exact resolve eq14472 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq14472
  have eq14519 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12670 eq14490
    | exact resolve eq14490 eq12670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12670 eq14490
  have eq14531 : ∀ X1 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (M.op (σ (M.op x y)) X1) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X1
    first
    | exact superpose eq11553 eq14517
    | exact resolve eq14517 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14517
  have eq14533 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14519
       have r₂ := eq11557
       grind)
    | exact resolve eq14519 eq11557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14519
  have eq14544 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14335 eq14531
    | exact resolve eq14531 eq14335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14335 eq14531
  have eq14548 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14533 eq14544
    | exact resolve eq14544 eq14533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14533 eq14544
  have eq14551 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq14548
    | exact resolve eq14548 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14548
  have eq14552 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11553 eq14551
    | exact resolve eq14551 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14551
  have eq14645 : x = (k x (τ (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq14552 eq241
    | exact resolve eq241 eq14552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq14552
  have eq14689 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq14645
    | exact resolve eq14645 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14645
  have eq14835 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq902 x x
       have i₂ := eq14689
       grind)
    | exact superpose eq14689 eq902
    | (have j0 := eq902 x x
       grind)
    | (have r₁ := eq902 x x
       have r₂ := eq14689
       grind)
    | exact resolve eq902 eq14689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq14689
  have eq14836 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq14835
  have eq14837 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq14836
  have eq14951 : (M.op (M.op x y) x) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq14837
       grind)
    | exact superpose eq14837 eq180
    | exact resolve eq180 eq14837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14837
  have eq14990 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13793 eq14951
    | exact resolve eq14951 eq13793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13793 eq14951
  have eq15007 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13858 eq14990
    | exact resolve eq14990 eq13858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13858 eq14990
  have eq15008 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15007
  have eq15028 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15008 eq31
    | exact resolve eq31 eq15008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15039 : (k y (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15008 eq116
    | exact resolve eq116 eq15008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq15040 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15008 eq132
    | exact resolve eq132 eq15008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq15137 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15008 eq12493
    | exact resolve eq12493 eq15008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15154 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq15137
  have eq15262 : (k (M.op x y) x) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq15040
    | exact resolve eq15040 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq15040
  have eq15263 : (k x (M.op x y)) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq99 eq15039
    | exact resolve eq15039 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq15039
  have eq15274 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq15028
    | exact resolve eq15028 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15028
  have eq15279 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12624 eq15262
    | exact resolve eq15262 eq12624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12624 eq15262
  have eq15283 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq15274
       grind)
    | exact superpose eq15274 eq24
    | exact resolve eq24 eq15274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15290 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq810 X0
       have i₂ := eq15274
       grind)
    | exact superpose eq15274 eq810
    | exact resolve eq810 eq15274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq15291 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq861
       have i₂ := eq15274
       grind)
    | exact superpose eq15274 eq861
    | exact resolve eq861 eq15274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq15296 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1792
       have i₂ := eq15274
       grind)
    | exact superpose eq15274 eq1792
    | exact resolve eq1792 eq15274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq15301 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1919
       have i₂ := eq15274
       grind)
    | exact superpose eq15274 eq1919
    | exact resolve eq1919 eq15274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq15308 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3035
       have i₂ := eq15274
       grind)
    | exact superpose eq15274 eq3035
    | exact resolve eq3035 eq15274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq15316 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq15308
  have eq15325 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq15301
  have eq15330 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq15296
  have eq15332 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq15291
  have eq15337 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11096 eq15316
    | exact resolve eq15316 eq11096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11096 eq15316
  have eq15338 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15337
  have eq15348 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11553 eq15325
    | exact resolve eq15325 eq11553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11553 eq15325
  have eq15349 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15348
  have eq15358 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10967 eq15330
    | exact resolve eq15330 eq10967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10967 eq15330
  have eq15359 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15358
  have eq15366 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have j1 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq15332
       have r₂ := eq13 (M.op x y) x
       grind)
    | exact resolve eq15332 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15332
  have eq15367 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12601 eq15290
    | (have j0 := eq15290 X0
       have j1 := eq12601 X0
       grind)
    | exact resolve eq15290 eq12601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12601 eq15290
  have eq15368 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq15367 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15367
  have eq15371 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq15283
    | exact resolve eq15283 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15283
  have eq15379 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15349 eq15359
    | exact resolve eq15359 eq15349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15349 eq15359
  have eq15380 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq15379
  have eq15381 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15279 eq15366
    | exact resolve eq15366 eq15279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15279 eq15366
  have eq15382 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq15381
  have eq15384 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15382 eq39
    | exact resolve eq39 eq15382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15382
  have eq15387 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq15384
    | exact resolve eq15384 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15384
  have eq15463 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15371 eq15387
    | exact resolve eq15387 eq15371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15371 eq15387
  have eq15464 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq15463
  have eq15513 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12493 eq15464
    | exact resolve eq15464 eq12493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12493 eq15464
  have eq15514 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15513
  have eq15689 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15154 eq13802
    | exact resolve eq13802 eq15154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13802 eq15154
  have eq15701 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq15689
  have eq15708 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15701
       have r₂ := eq11557
       grind)
    | exact resolve eq15701 eq11557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11557 eq15701
  have eq15711 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15274 eq15708
    | exact resolve eq15708 eq15274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15708
  have eq15868 : (M.op (M.op x y) x) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq15711
       grind)
    | exact superpose eq15711 eq180
    | exact resolve eq180 eq15711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15907 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15711 eq15868
    | exact resolve eq15868 eq15711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15868
  have eq15939 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15907 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq15907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15907
  have eq15961 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq15939
  have eq15989 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq15961
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq15961 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961
  have eq17315 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15263 eq12658
    | exact resolve eq12658 eq15263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12658 eq15263
  have eq17326 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17315
  have eq17344 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15274 eq17326
    | exact resolve eq17326 eq15274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15274 eq17326
  have eq17350 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15989 eq17344
    | exact resolve eq17344 eq15989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15989 eq17344
  have eq17351 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq17350
  have eq17370 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15711
       have i₂ := eq17351
       grind)
    | exact superpose eq17351 eq15711
    | exact resolve eq15711 eq17351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15711 eq17351
  have eq17399 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq17370
  have eq17425 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq17399
       grind)
    | exact superpose eq17399 eq18
    | exact resolve eq18 eq17399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17426 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq17399
       grind)
    | exact superpose eq17399 eq24
    | exact resolve eq24 eq17399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17429 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq187
       have i₂ := eq17399
       grind)
    | exact superpose eq17399 eq187
    | exact resolve eq187 eq17399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17483 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq17426
    | exact resolve eq17426 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17426
  have eq21729 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15338 eq869
    | (have j0 := eq869 (M.op x y) (M.op x y) x
       grind)
    | exact resolve eq869 eq15338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15338
  have eq21732 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21729 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21729
  have eq21738 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15368 eq21732
    | exact resolve eq21732 eq15368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21732
  have eq21742 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17425 eq21738
    | exact resolve eq21738 eq17425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21738
  have eq21743 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21742
  have eq23137 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21743 eq17429
    | exact resolve eq17429 eq21743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21743
  have eq23179 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq23137
  have eq23195 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq23179
    | exact resolve eq23179 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23179
  have eq23202 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15380 eq23195
    | exact resolve eq23195 eq15380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23195
  have eq23206 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1846 (σ y)
       grind)
    | (have r₁ := eq23202
       have r₂ := eq1846 (σ y)
       grind)
    | (have r₁ := eq23202
       have r₂ := eq1846 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq23202 eq1846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1846 eq23202
  have eq23230 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23206 eq1858
    | exact resolve eq1858 eq23206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1858 eq23206
  have eq23274 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq23230
  have eq23307 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23274 eq27
    | exact resolve eq27 eq23274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23274
  have eq23397 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq23307
       have r₂ := eq15380
       grind)
    | exact resolve eq23307 eq15380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15380 eq23307
  have eq23423 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23397 eq849
    | (have r₁ := eq849
       have r₂ := eq23397
       grind)
    | exact resolve eq849 eq23397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq23397
  have eq23425 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq23423
  have eq23429 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15514 eq23425
    | exact resolve eq23425 eq15514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15514 eq23425
  have eq23430 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq23429
  have eq23459 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23430 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq23430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23430
  have eq23485 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq23459
  have eq23577 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23485 eq115
    | exact resolve eq115 eq23485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq23607 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq23577
    | exact resolve eq23577 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23577
  have eq23611 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15008 eq23607
    | exact resolve eq23607 eq15008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15008 eq23607
  have eq23737 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq23611 eq869
    | (have j0 := eq869 (M.op x y) (M.op x y) x
       grind)
    | exact resolve eq869 eq23611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23611
  have eq23740 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq23737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23737
  have eq23747 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15368 eq23740
    | exact resolve eq23740 eq15368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15368 eq23740
  have eq23751 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17425 eq23747
    | exact resolve eq23747 eq17425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17425 eq23747
  have eq23752 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq23751
  have eq23791 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23752 eq17429
    | exact resolve eq17429 eq23752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17429 eq23752
  have eq23833 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq23791
  have eq23848 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq23833
    | exact resolve eq23833 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23833
  have eq23855 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17483 eq23848
    | exact resolve eq23848 eq17483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17483 eq23848
  have eq23859 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq23485 eq23855
    | exact resolve eq23855 eq23485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23485 eq23855
  have eq23860 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq23859
  have eq23865 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq23860 eq31
    | exact resolve eq31 eq23860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23860
  have eq24152 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq23865
    | exact resolve eq23865 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23865
  have eq24173 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17399 eq24152
    | exact resolve eq24152 eq17399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17399 eq24152
  have eq24174 : x = (M.op x y) := by grind
  clear eq24173
  have eq24181 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq24174
       grind)
    | exact superpose eq24174 eq18
    | exact resolve eq18 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24182 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq24174
       grind)
    | exact superpose eq24174 eq22
    | exact resolve eq22 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq24184 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq24174
       grind)
    | exact superpose eq24174 eq39
    | exact resolve eq39 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq24185 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq24174
       grind)
    | exact superpose eq24174 eq180
    | exact resolve eq180 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq24188 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq199
       have i₂ := eq24174
       grind)
    | exact superpose eq24174 eq199
    | exact resolve eq199 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq24192 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y (M.op x y)) := by
    first
    | (have i₁ := eq847
       have i₂ := eq24174
       grind)
    | exact superpose eq24174 eq847
    | (have r₁ := eq847
       have r₂ := eq24174
       grind)
    | exact resolve eq847 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq24194 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq24192
  have eq24196 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq24182 eq20
    | exact resolve eq20 eq24182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24232 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq24182 eq438
    | exact resolve eq438 eq24182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq25241 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq24188
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq24188
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq24188 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24188
  have eq25294 : (k (M.op x y) (M.op x y)) = (M.op (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq25241
  have eq27101 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq24194 eq36
    | exact resolve eq36 eq24194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq27111 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq27101
    | exact resolve eq27101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27101
  have eq27116 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq24196 eq27111
    | exact resolve eq27111 eq24196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27111
  have eq27132 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27116 eq863
    | exact resolve eq863 eq27116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27116
  have eq27146 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq27132
  have eq30796 : y = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27146 eq259
    | exact resolve eq259 eq27146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq27146
  have eq30886 : y = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq29 eq30796
    | exact resolve eq30796 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30796
  have eq30910 : y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq30886
       have i₂ := eq24174
       grind)
    | exact superpose eq24174 eq30886
    | exact resolve eq30886 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30886
  have eq30933 : y = (k y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq30910
       have r₂ := eq13 y (M.op x y)
       grind)
    | exact resolve eq30910 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30910
  have eq30988 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30933 eq24194
    | exact resolve eq24194 eq30933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24194
  have eq30993 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30933 eq24184
    | exact resolve eq24184 eq30933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30933
  have eq31017 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq30993
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30993
    | exact resolve eq30993 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30993
  have eq31036 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31017 eq863
    | exact resolve eq863 eq31017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863 eq31017
  have eq31045 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31036
  have eq31176 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq947 y
       have i₂ := eq30988
       grind)
    | exact superpose eq30988 eq947
    | exact resolve eq947 eq30988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq31179 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq30988
       grind)
    | exact superpose eq30988 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq30988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30988
  have eq31210 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31179
  have eq31241 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24181 eq31176
    | exact resolve eq31176 eq24181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31176
  have eq31379 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31045 eq967
    | exact resolve eq967 eq31045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31380 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31045 eq812
    | exact resolve eq812 eq31045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31457 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq31379
    | exact resolve eq31379 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31379
  have eq31532 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq31210
       grind)
    | exact superpose eq31210 eq40
    | exact resolve eq40 eq31210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31210
  have eq31569 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31532
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31532
    | exact resolve eq31532 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31532
  have eq31573 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq31569
    | exact resolve eq31569 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31569
  have eq31576 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24196 eq31573
    | exact resolve eq31573 eq24196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31573
  have eq31583 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31241 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq31241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31241
  have eq31614 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq31583
  have eq31630 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq31614
       have r₂ := eq13 (M.op x y) y
       grind)
    | exact resolve eq31614 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31614
  have eq31677 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31457 eq967
    | exact resolve eq967 eq31457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31791 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31576 eq914
    | (have j0 := eq914 (σ y) X0
       grind)
    | (have r₁ := eq914 (σ y) (σ x)
       have r₂ := eq31576
       grind)
    | exact resolve eq914 eq31576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq31794 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31576 eq869
    | (have j0 := eq869 (σ y) (σ y) x
       grind)
    | exact resolve eq869 eq31576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869
  have eq31797 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq31794 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31794
  have eq31809 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq812 eq31797
    | (have j0 := eq31797 (σ x)
       grind)
    | exact resolve eq31797 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812 eq31797
  have eq31814 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq31809
    | exact resolve eq31809 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31809
  have eq31826 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31630 eq40
    | exact resolve eq40 eq31630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq31630
  have eq31832 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq31826
    | exact resolve eq31826 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31826
  have eq31838 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24196 eq31832
    | exact resolve eq31832 eq24196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31832
  have eq31852 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31677 eq12
    | (have j0 := eq12 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq31677
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq31677
       grind)
    | exact resolve eq12 eq31677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31677
  have eq31881 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31852
  have eq31896 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31045 eq31881
    | exact resolve eq31881 eq31045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31045 eq31881
  have eq31897 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31896
  have eq32918 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31380 eq31457
    | exact resolve eq31457 eq31380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31380 eq31457
  have eq32960 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32918
  have eq33040 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32960 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq32960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32960
  have eq33070 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33040
  have eq33521 : (k (M.op x y) (M.op x y)) ≠ (k (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq25294 eq12
    | (have j0 := eq12 (M.op x y) (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq12 (M.op x y) (k (M.op x y) (M.op x y))
       have r₂ := eq25294
       grind)
    | (have r₁ := eq12 (M.op x y) (M.op x y)
       have r₂ := eq25294
       grind)
    | exact resolve eq12 eq25294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25294
  have eq33557 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (k (M.op x y) (M.op x y)) = (k (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq33521
  have eq33583 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq915 eq33557
    | (have j1 := eq915 (M.op x y)
       grind)
    | exact resolve eq33557 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915 eq33557
  have eq33601 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq33583
       have r₂ := eq13 (M.op x y) (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq33583
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq33583 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33583
  have eq33782 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq33601 eq24185
    | exact resolve eq24185 eq33601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24185 eq33601
  have eq45402 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31814 eq967
    | exact resolve eq967 eq31814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq31814
  have eq45661 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33070 eq31838
    | exact resolve eq31838 eq33070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31838
  have eq45666 : (k (M.op x y) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33070 eq24232
    | exact resolve eq24232 eq33070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24232 eq33070
  have eq45674 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45661
  have eq45691 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq45666
    | exact resolve eq45666 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45666
  have eq45697 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45674 eq45691
    | exact resolve eq45691 eq45674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45691
  have eq45746 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45674 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq45674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45674
  have eq45783 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq45746
  have eq46155 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45402 eq12
    | (have j0 := eq12 (σ y) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ y) (M.op (σ x) (σ y))
       have r₂ := eq45402
       grind)
    | (have r₁ := eq12 (σ y) (σ y)
       have r₂ := eq45402
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq45402
       grind)
    | exact resolve eq12 eq45402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45402
  have eq46191 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46155
  have eq46214 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31897 eq46191
    | exact resolve eq46191 eq31897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31897 eq46191
  have eq46215 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq46214
  have eq63786 : (k (σ (M.op x y)) (σ x)) = (σ (τ (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45697 eq24184
    | exact resolve eq24184 eq45697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24184 eq45697
  have eq63818 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63786
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq63786
    | exact resolve eq63786 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63786
  have eq63831 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq63818
    | exact resolve eq63818 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63818
  have eq63837 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24196 eq63831
    | exact resolve eq63831 eq24196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63831
  have eq64569 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq45783 eq97
    | exact resolve eq97 eq45783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq45783
  have eq64664 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64569
       have i₂ := eq24174
       grind)
    | exact superpose eq24174 eq64569
    | exact resolve eq64569 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64569
  have eq64675 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq64664
    | exact resolve eq64664 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64664
  have eq64778 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64675 eq33782
    | exact resolve eq33782 eq64675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33782 eq64675
  have eq64803 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq64778
  have eq64839 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq24181 eq64803
    | exact resolve eq64803 eq24181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64803
  have eq64840 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq64839
  have eq64919 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq64840 eq46215
    | exact resolve eq46215 eq64840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46215 eq64840
  have eq64925 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq64919
  have eq64979 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq31791 (σ y)
       grind)
    | (have r₁ := eq64925
       have r₂ := eq31791 (σ y)
       grind)
    | (have r₁ := eq64925
       have r₂ := eq31791 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq64925 eq31791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31791 eq64925
  have eq64984 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq64979
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq64979 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64979
  have eq64986 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31576 eq64984
    | exact resolve eq64984 eq31576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31576 eq64984
  have eq64992 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq64986 eq27
    | exact resolve eq27 eq64986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64986
  have eq65007 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq64992
       have r₂ := eq24196
       grind)
    | exact resolve eq64992 eq24196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64992
  have eq65009 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq65007 eq31
    | exact resolve eq31 eq65007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq65007
  have eq65349 : x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq65009
    | exact resolve eq65009 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq65009
  have eq65370 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq65349
       have i₂ := eq24174
       grind)
    | exact superpose eq24174 eq65349
    | exact resolve eq65349 eq24174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24174 eq65349
  have eq65371 : y = (M.op x y) := by grind
  clear eq65370
  have eq65374 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq65371
       grind)
    | exact superpose eq65371 eq24
    | exact resolve eq24 eq65371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq65377 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq187
       have i₂ := eq65371
       grind)
    | exact superpose eq65371 eq187
    | exact resolve eq187 eq65371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq65404 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq24181
       have i₂ := eq65371
       grind)
    | exact superpose eq65371 eq24181
    | exact resolve eq24181 eq65371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24181 eq65371
  have eq65445 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq65404 eq65377
    | exact resolve eq65377 eq65404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65377 eq65404
  have eq65448 : (σ x) = (σ y) := by
    first
    | exact superpose eq24182 eq65374
    | exact resolve eq65374 eq24182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24182 eq65374
  have eq65453 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq65445
    | exact resolve eq65445 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq65445
  have eq65455 : (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq24196 eq65453
    | exact resolve eq65453 eq24196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65453
  have eq65456 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq65448 eq65455
    | exact resolve eq65455 eq65448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65455
  have eq65457 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq65448 eq26
    | exact resolve eq26 eq65448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq65990 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65456 eq63837
    | exact resolve eq63837 eq65456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63837 eq65456
  have eq66008 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq65990
  have eq66018 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq65448 eq66008
    | exact resolve eq66008 eq65448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66008
  have eq66019 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq66018
  have eq66035 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65457 eq66019
    | exact resolve eq66019 eq65457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65457 eq66019
  have eq66040 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65448 eq66035
    | exact resolve eq66035 eq65448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65448 eq66035
  have eq66041 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq66040
  have eq66048 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq66041 eq27
    | exact resolve eq27 eq66041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq66041
  have eq66068 : False := by grind
  exact eq66068

/-- `Equation4438`: `x ◇ (y ◇ x) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pxy_x_pxy_Equation4438 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4438 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4438.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X0) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq13 (M.op X0 X0) X1
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
  have eq176 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) x) := by
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
  have eq181 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X0 X2) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X0 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X2) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have r₁ := eq13 (M.op X0 (M.op X1 X0)) X0
       have r₂ := eq16 X0 X1 (M.op X1 X0)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
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
  have eq186 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x X1) x) := by
    intro X1
    first
    | (have i₁ := eq16 x x X1
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X1) (σ x)) := by
    intro X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X2 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 y X0 x
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq182
    | (have j0 := eq182 (σ y) X0 (σ x)
       grind)
    | exact resolve eq182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq719 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) (σ y)) := by
    intro X1
    first
    | exact superpose eq667 eq16
    | (have j0 := eq16 (σ y) (σ x) X1
       grind)
    | exact resolve eq16 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (k X0 X1) X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq807 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (k X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq28 X0 (M.op X1 X0)
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 (M.op X1 X0)
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op x (k X0 x)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq28 X0 x
       grind)
    | exact superpose eq28 eq180
    | (have j1 := eq28 X0 x
       grind)
    | exact resolve eq180 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq821 : (M.op x y) = (k x y) ∨ y = (M.op x x) := by
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
  have eq830 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq837 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq839 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq852 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq821
       grind)
    | exact superpose eq821 eq41
    | exact resolve eq41 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq852
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq852
    | exact resolve eq852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq855 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq853
    | exact resolve eq853 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq855 eq830
    | exact resolve eq830 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq865
       have r₂ := eq27
       grind)
    | exact resolve eq865 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq879 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (M.op (σ x) X0) ∨ (σ x) = (k (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq872 eq12
    | (have j0 := eq12 (σ x) X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq872
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq872
       grind)
    | exact resolve eq12 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq872 eq13
    | exact resolve eq13 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq882 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq872 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq892 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq880
       have r₂ := eq882
       grind)
    | exact resolve eq880 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880 eq882
  have eq896 : (τ (σ y)) = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq892 eq98
    | exact resolve eq98 eq892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq892
  have eq902 : y = (k x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq32 eq896
    | exact resolve eq896 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896
  have eq1465 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j0 := eq879 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879
  have eq1466 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq1465
    | exact resolve eq1465 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1473 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1466 eq153
    | exact resolve eq153 eq1466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1466
  have eq1478 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq1473
    | exact resolve eq1473 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1481 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq821 eq1478
    | exact resolve eq1478 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821 eq1478
  have eq1513 : (M.op (M.op x y) x) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq189 x
       have i₂ := eq1481
       grind)
    | exact superpose eq1481 eq189
    | exact resolve eq189 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1514 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq1481
       grind)
    | exact superpose eq1481 eq180
    | exact resolve eq180 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1519 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq176 x x X0
       have i₂ := eq1481
       grind)
    | exact superpose eq1481 eq176
    | exact resolve eq176 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1530 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1519 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1519
    | (have j0 := eq1519 X0
       grind)
    | exact resolve eq1519 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq1533 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1514
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1514
    | exact resolve eq1514 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq1537 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1530 x
       have i₂ := eq189 x
       grind)
    | (have i₁ := eq1530 y
       have i₂ := eq189 x
       grind)
    | exact superpose eq189 eq1530
    | (have j0 := eq1530 y
       grind)
    | exact resolve eq1530 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq1530
  have eq1538 : (M.op x y) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1533 eq1537
    | exact resolve eq1537 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq1589 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1533 eq13
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq1533
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1533
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1533
       grind)
    | exact resolve eq13 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1590 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1533 eq16
    | exact resolve eq16 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1598 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1589
  have eq1609 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1538 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1641 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1598 eq40
    | exact resolve eq40 eq1598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1598
  have eq1642 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1641
    | exact resolve eq1641 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1641
  have eq1690 : (k y x) = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq1513
       grind)
    | exact superpose eq1513 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1700 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1533 eq1690
    | exact resolve eq1690 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq1778 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq839 x
       have i₂ := eq1481
       grind)
    | exact superpose eq1481 eq839
    | exact resolve eq839 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1799 : x = (M.op x y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1778
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1778
    | exact resolve eq1778 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1778
  have eq1800 : x = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1799
  have eq1950 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1800
       grind)
    | exact superpose eq1800 eq41
    | exact resolve eq41 eq1800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1953 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1950
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1950
    | exact resolve eq1950 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950
  have eq1959 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1953 eq830
    | exact resolve eq830 eq1953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq1963 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1959
  have eq1970 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1963 eq196
    | exact resolve eq196 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1971 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1963 eq181
    | exact resolve eq181 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1977 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1963 eq176
    | exact resolve eq176 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1989 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1977
    | (have j0 := eq1977 X0
       grind)
    | exact resolve eq1977 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq1991 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1971
    | exact resolve eq1971 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1971
  have eq1995 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq1989
    | (have j0 := eq1989 (σ y)
       grind)
    | exact resolve eq1989 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq1996 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1991 eq1995
    | exact resolve eq1995 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995
  have eq2006 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1991 eq176
    | exact resolve eq176 eq1991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1991
  have eq2016 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq196 eq2006
    | (have j0 := eq2006 (σ y)
       grind)
    | exact resolve eq2006 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2019 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1970 eq2016
    | exact resolve eq2016 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2016
  have eq2020 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1996 eq2019
    | exact resolve eq2019 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2021 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1996 eq2020
    | exact resolve eq2020 eq1996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1996 eq2020
  have eq2196 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2021 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2763 : ∀ X0 : G, (k x (M.op X0 x)) = (M.op y x) ∨ y = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq807 x x x
       have i₂ := eq1481
       grind)
    | exact superpose eq1481 eq807
    | exact resolve eq807 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq2916 : ∀ X0 : G, (M.op (M.op x y) x) = (k x (M.op X0 x)) ∨ y = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1513 eq2763
    | (have j0 := eq2763 X0
       grind)
    | exact resolve eq2763 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513 eq2763
  have eq2928 : ∀ X0 : G, (M.op x y) = (k x (M.op X0 x)) ∨ y = (M.op X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1533 eq2916
    | (have j0 := eq2916 X0
       grind)
    | exact resolve eq2916 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916
  have eq3150 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1609 eq36
    | exact resolve eq36 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609
  have eq3155 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3150
    | exact resolve eq3150 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3150
  have eq3171 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1700
       grind)
    | exact superpose eq1700 eq40
    | exact resolve eq40 eq1700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1700
  have eq3175 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3171
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3171
    | exact resolve eq3171 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3171
  have eq3177 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq3175
    | exact resolve eq3175 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3175
  have eq3192 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3155 eq800
    | (have j0 := eq800 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq800 eq3155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3155
  have eq3193 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq181 eq3192
    | exact resolve eq3192 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3192
  have eq3197 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1481 eq3193
    | exact resolve eq3193 eq1481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1481 eq3193
  have eq3199 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1963 eq3197
    | exact resolve eq3197 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197
  have eq3200 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1970 eq3199
    | exact resolve eq3199 eq1970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970 eq3199
  have eq3201 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2021 eq3200
    | exact resolve eq3200 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3200
  have eq3231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2196 eq3177
    | exact resolve eq3177 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3239 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq3231
  have eq3246 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3239
       have r₂ := eq27
       grind)
    | exact resolve eq3239 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3239
  have eq3260 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3246 eq667
    | exact resolve eq667 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq3261 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3246 eq839
    | exact resolve eq839 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839
  have eq3263 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3246 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3246
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3246
       grind)
    | exact resolve eq13 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3265 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3246 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246
  have eq3285 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3263
       have r₂ := eq3265
       grind)
    | exact resolve eq3263 eq3265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3263 eq3265
  have eq3286 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2021 eq3261
    | exact resolve eq3261 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261
  have eq3287 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2021 eq3260
    | exact resolve eq3260 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021 eq3260
  have eq3315 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3287 eq719
    | exact resolve eq719 eq3287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719 eq3287
  have eq3358 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3315 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ y)
       have r₂ := eq3315
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3315
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq3315
       grind)
    | exact resolve eq13 eq3315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315
  have eq3370 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq3358
  have eq4228 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3201 eq16
    | exact resolve eq16 eq3201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4229 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3201 eq28
    | (have j0 := eq28 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq28 eq3201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4233 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3201 eq177
    | exact resolve eq177 eq3201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4248 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1642 eq4229
    | exact resolve eq4229 eq1642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4229
  have eq4257 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4248
       have r₂ := eq27
       grind)
    | exact resolve eq4248 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4248
  have eq4270 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4257 eq176
    | exact resolve eq176 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq4272 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4257 eq177
    | exact resolve eq177 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq4273 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) = (M.op (M.op (σ x) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4257 eq178
    | exact resolve eq178 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4277 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4257 eq182
    | exact resolve eq182 eq4257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq4257
  have eq4281 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3201 eq4277
    | exact resolve eq4277 eq3201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4277
  have eq4285 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4228 eq4273
    | exact resolve eq4273 eq4228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4273
  have eq4286 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4272 eq4270
    | exact resolve eq4270 eq4272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4270 eq4272
  have eq4291 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3201 eq4286
    | exact resolve eq4286 eq3201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3201 eq4286
  have eq4417 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1 (M.op X1 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq4690 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1533 eq2928
    | exact resolve eq2928 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2928
  have eq4701 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4690
  have eq4723 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4701 eq36
    | exact resolve eq36 eq4701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4701
  have eq4727 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4723
    | exact resolve eq4723 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4723
  have eq5862 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ (M.op x y)) X1) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq4281 eq178
    | exact resolve eq178 eq4281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5898 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4233 eq5862
    | exact resolve eq5862 eq4233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4233 eq5862
  have eq5925 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4291 eq178
    | exact resolve eq178 eq4291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq5944 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (M.op (σ x) (σ (M.op x y))) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4228 eq5925
    | exact resolve eq5925 eq4228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4228 eq5925
  have eq5956 : (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4285 eq5944
    | exact resolve eq5944 eq4285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4285 eq5944
  have eq5960 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5898 eq5956
    | exact resolve eq5956 eq5898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5898 eq5956
  have eq6714 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5960 eq4281
    | exact resolve eq4281 eq5960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281 eq5960
  have eq6735 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6714
  have eq6755 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6735 eq4291
    | exact resolve eq4291 eq6735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4291 eq6735
  have eq6775 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6755
  have eq6790 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6775 eq28
    | (have j0 := eq28 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq28 eq6775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6775
  have eq6822 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4727 eq6790
    | exact resolve eq6790 eq4727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4727 eq6790
  have eq6829 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6822
       have r₂ := eq27
       grind)
    | exact resolve eq6822 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6822
  have eq6833 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1963 eq6829
    | exact resolve eq6829 eq1963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1963 eq6829
  have eq6834 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6833
  have eq6838 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6834 eq27
    | exact resolve eq27 eq6834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6839 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6834 eq186
    | (have r₁ := eq186
       have r₂ := eq6834
       grind)
    | exact resolve eq186 eq6834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6876 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6839
  have eq6920 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6876 eq855
    | exact resolve eq855 eq6876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6876
  have eq6930 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6920
       have r₂ := eq6838
       grind)
    | exact resolve eq6920 eq6838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6838 eq6920
  have eq6950 : x ≠ y ∨ y = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq6930
       grind)
    | exact superpose eq6930 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq6930
       grind)
    | exact resolve eq13 eq6930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6952 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq6930
       grind)
    | exact superpose eq6930 eq28
    | exact resolve eq28 eq6930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6930
  have eq6985 : y = (k x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6950
       have r₂ := eq6952
       grind)
    | exact resolve eq6950 eq6952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6950 eq6952
  have eq8618 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3286 eq3177
    | exact resolve eq3177 eq3286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3177 eq3286
  have eq8628 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8618
  have eq8638 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6834 eq8628
    | exact resolve eq8628 eq6834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8628
  have eq8657 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8638 eq1590
    | exact resolve eq1590 eq8638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8638
  have eq8683 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8657
  have eq8715 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1533 eq8683
    | exact resolve eq8683 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8683
  have eq8716 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8715
  have eq8775 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8716 eq3370
    | exact resolve eq3370 eq8716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3370
  have eq8795 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq8716
  have eq8809 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq8775
  have eq8833 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq8809
       have r₂ := eq8795
       grind)
    | exact resolve eq8809 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8809
  have eq8853 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq3285 eq8833
    | exact resolve eq8833 eq3285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285 eq8833
  have eq8866 : x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq8853
       have r₂ := eq8795
       grind)
    | exact resolve eq8853 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8795 eq8853
  have eq8877 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6834 eq8866
    | exact resolve eq8866 eq6834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6834 eq8866
  have eq8988 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq8877 eq1590
    | exact resolve eq1590 eq8877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1590 eq8877
  have eq9014 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq8988
  have eq9046 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1533 eq9014
    | exact resolve eq9014 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9014
  have eq9047 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9046
  have eq9064 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9047 eq27
    | exact resolve eq27 eq9047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9065 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9047 eq186
    | (have r₁ := eq186
       have r₂ := eq9047
       grind)
    | exact resolve eq186 eq9047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9104 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9065
  have eq9152 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9104 eq855
    | exact resolve eq855 eq9104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9104
  have eq9159 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq9152
       have r₂ := eq9064
       grind)
    | exact resolve eq9152 eq9064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9064 eq9152
  have eq9177 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq9159
       grind)
    | exact superpose eq9159 eq180
    | exact resolve eq180 eq9159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9182 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq9159
       grind)
    | exact superpose eq9159 eq28
    | exact resolve eq28 eq9159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9216 : y = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6985 eq9182
    | exact resolve eq9182 eq6985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6985 eq9182
  have eq9217 : y = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq9216
  have eq9220 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq9177
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9177
    | exact resolve eq9177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9177
  have eq9465 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq9217
       grind)
    | exact superpose eq9217 eq40
    | exact resolve eq40 eq9217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9217
  have eq9470 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq9465
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9465
    | exact resolve eq9465 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9465
  have eq9472 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq9470
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9470
    | exact resolve eq9470 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9470
  have eq9569 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq9472 eq800
    | (have j0 := eq800 (σ x) (σ x) x
       grind)
    | exact resolve eq800 eq9472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9570 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq181 eq9569
    | exact resolve eq9569 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9569
  have eq9574 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9047 eq9570
    | exact resolve eq9570 eq9047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9570
  have eq9577 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28 eq9574
    | (have j1 := eq28 (σ x) (σ x)
       grind)
    | exact resolve eq9574 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9574
  have eq9578 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9472 eq9577
    | exact resolve eq9577 eq9472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9472 eq9577
  have eq11456 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9578 eq181
    | exact resolve eq181 eq9578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9578
  have eq11498 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq11456
    | exact resolve eq11456 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11456
  have eq11515 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9047 eq11498
    | exact resolve eq11498 eq9047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11498
  have eq11516 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11515
  have eq11548 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11516 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq11516
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq11516
       grind)
    | exact resolve eq13 eq11516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11516
  have eq11568 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11548
  have eq11609 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq11568 eq142
    | exact resolve eq142 eq11568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq11568
  have eq11622 : x = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq11609
    | exact resolve eq11609 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11609
  have eq11917 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq837 x
       have i₂ := eq11622
       grind)
    | exact superpose eq11622 eq837
    | (have j0 := eq837 x
       grind)
    | (have r₁ := eq837 x
       have r₂ := eq11622
       grind)
    | exact resolve eq837 eq11622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11622
  have eq11919 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11917
  have eq11958 : (M.op (M.op x y) x) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq11919
       grind)
    | exact superpose eq11919 eq180
    | exact resolve eq180 eq11919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11919
  have eq12006 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9159 eq11958
    | exact resolve eq11958 eq9159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9159 eq11958
  have eq12022 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9220 eq12006
    | exact resolve eq12006 eq9220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9220 eq12006
  have eq12040 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12022 eq29
    | exact resolve eq29 eq12022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq12022
  have eq12080 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq12040
    | exact resolve eq12040 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq12040
  have eq12081 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq12080
  have eq12093 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12081
       grind)
    | exact superpose eq12081 eq18
    | exact resolve eq18 eq12081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12094 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq12081
       grind)
    | exact superpose eq12081 eq24
    | exact resolve eq24 eq12081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12097 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq665 X0
       have i₂ := eq12081
       grind)
    | exact superpose eq12081 eq665
    | exact resolve eq665 eq12081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq12171 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq12094
    | exact resolve eq12094 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12094
  have eq12261 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12171 eq1642
    | exact resolve eq1642 eq12171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1642
  have eq12273 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12261
  have eq12310 : (M.op (M.op x y) (M.op x y)) = (k (M.op (M.op x y) (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12093 eq4417
    | exact resolve eq4417 eq12093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4417 eq12093
  have eq12457 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12273 eq2196
    | exact resolve eq2196 eq12273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196 eq12273
  have eq12468 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq12457
  have eq12685 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k X0 (M.op x y))) ∨ x = (M.op x y) ∨ (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq12097 X0
       have i₂ := eq28 X0 sF0
       grind)
    | exact superpose eq28 eq12097
    | (have j1 := eq28 (M.op x y) (M.op (M.op x y) (k X0 (M.op x y)))
       grind)
    | exact resolve eq12097 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12097
  have eq13032 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12310 eq42
    | exact resolve eq42 eq12310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq12310
  have eq13038 : (σ (M.op (M.op x y) (M.op x y))) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12171 eq13032
    | exact resolve eq13032 eq12171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13032
  have eq14016 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12468 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq12468
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12468
       grind)
    | exact resolve eq13 eq12468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14018 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12468 eq28
    | exact resolve eq28 eq12468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12468
  have eq14057 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq14016
       have r₂ := eq14018
       grind)
    | exact resolve eq14016 eq14018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14016 eq14018
  have eq14109 : (τ (σ x)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14057 eq116
    | exact resolve eq116 eq14057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq14120 : x = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14109
    | exact resolve eq14109 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14109
  have eq14124 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12081 eq14120
    | exact resolve eq14120 eq12081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14120
  have eq16770 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14124 eq12685
    | (have j0 := eq12685 (M.op x y)
       grind)
    | exact resolve eq12685 eq14124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12685
  have eq16819 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16770
  have eq16841 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq16819
    | (have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq16819 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16819
  have eq16847 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1533 eq16841
    | exact resolve eq16841 eq1533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533 eq16841
  have eq16849 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq837 (M.op x y)
       grind)
    | (have r₁ := eq16847
       have r₂ := eq837 (M.op x y)
       grind)
    | exact resolve eq16847 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq16847
  have eq16871 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16849 eq13038
    | exact resolve eq13038 eq16849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13038
  have eq16890 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16849 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq16849
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq16849
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq16849
       grind)
    | exact resolve eq13 eq16849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16849
  have eq16910 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16890
  have eq16927 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16871
  have eq16950 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16927
    | exact resolve eq16927 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16927
  have eq16957 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9047 eq16950
    | exact resolve eq16950 eq9047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9047 eq16950
  have eq16962 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq14057 eq16957
    | exact resolve eq16957 eq14057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14057 eq16957
  have eq16966 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16962 eq27
    | exact resolve eq27 eq16962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16962
  have eq17097 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16966
       have r₂ := eq12171
       grind)
    | exact resolve eq16966 eq12171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16966
  have eq17685 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16910 eq14124
    | exact resolve eq14124 eq16910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14124 eq16910
  have eq17694 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq17685
  have eq17708 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17097 eq17694
    | exact resolve eq17694 eq17097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17097 eq17694
  have eq17709 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17708
  have eq17722 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17709 eq27
    | exact resolve eq27 eq17709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17723 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17709 eq186
    | (have r₁ := eq186
       have r₂ := eq17709
       grind)
    | exact resolve eq186 eq17709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq17762 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17723
  have eq17840 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12171 eq17722
    | exact resolve eq17722 eq12171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17845 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq17840
  have eq17857 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17762 eq855
    | exact resolve eq855 eq17762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855 eq17762
  have eq17868 : y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17857
       have r₂ := eq17722
       grind)
    | exact resolve eq17857 eq17722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17722 eq17857
  have eq17873 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12081 eq17868
    | exact resolve eq17868 eq12081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12081 eq17868
  have eq17943 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq17873
       grind)
    | exact superpose eq17873 eq28
    | exact resolve eq28 eq17873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17873
  have eq17962 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq17943
  have eq18032 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq17962
       grind)
    | exact superpose eq17962 eq40
    | exact resolve eq40 eq17962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq17962
  have eq18052 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18032
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18032
    | exact resolve eq18032 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18032
  have eq18054 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq18052
    | exact resolve eq18052 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18052
  have eq18056 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12171 eq18054
    | exact resolve eq18054 eq12171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12171 eq18054
  have eq18136 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18056 eq800
    | (have j0 := eq800 (σ x) (σ x) x
       grind)
    | exact resolve eq800 eq18056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq18143 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq181 eq18136
    | exact resolve eq18136 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18136
  have eq18147 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17709 eq18143
    | exact resolve eq18143 eq17709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18143
  have eq18151 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq18147
    | (have j1 := eq28 (σ x) (σ x)
       grind)
    | exact resolve eq18147 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18147
  have eq18154 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18056 eq18151
    | exact resolve eq18151 eq18056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18151
  have eq18515 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18154 eq181
    | exact resolve eq181 eq18154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18154
  have eq18562 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18515
    | exact resolve eq18515 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18515
  have eq18581 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17709 eq18562
    | exact resolve eq18562 eq17709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17709 eq18562
  have eq18582 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18581
  have eq18621 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18582 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq18582
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq18582
       grind)
    | exact resolve eq13 eq18582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18582
  have eq18641 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq18621
  have eq18712 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18641 eq18056
    | exact resolve eq18056 eq18641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18056 eq18641
  have eq18720 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq18712
  have eq18736 : x = (M.op x y) := by
    first
    | (have r₁ := eq18720
       have r₂ := eq17845
       grind)
    | exact resolve eq18720 eq17845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17845 eq18720
  have eq18755 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18736
       grind)
    | exact superpose eq18736 eq18
    | exact resolve eq18 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq18756 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq18736
       grind)
    | exact superpose eq18736 eq22
    | exact resolve eq22 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq18759 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq18736
       grind)
    | exact superpose eq18736 eq180
    | exact resolve eq180 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq18760 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq185
       have i₂ := eq18736
       grind)
    | exact superpose eq18736 eq185
    | (have r₁ := eq185
       have r₂ := eq18736
       grind)
    | exact resolve eq185 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq18765 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq902
       have i₂ := eq18736
       grind)
    | exact superpose eq18736 eq902
    | exact resolve eq902 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18790 : (M.op x y) = (k (M.op x y) y) := by grind
  clear eq18760
  have eq18804 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq18756 eq20
    | exact resolve eq20 eq18756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19031 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18790 eq41
    | exact resolve eq41 eq18790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq18790
  have eq19033 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq19031
    | exact resolve eq19031 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq19031
  have eq19035 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq18804 eq19033
    | exact resolve eq19033 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19033
  have eq19043 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19035 eq830
    | exact resolve eq830 eq19035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq19035
  have eq19074 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19043 eq196
    | exact resolve eq196 eq19043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq19076 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19043 eq181
    | exact resolve eq181 eq19043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19094 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19043 eq660
    | exact resolve eq660 eq19043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19104 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq19094
    | (have j0 := eq19094 X0
       grind)
    | exact resolve eq19094 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19094
  have eq19118 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq19076
    | exact resolve eq19076 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq19076
  have eq19120 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq181 eq19104
    | exact resolve eq19104 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19104
  have eq19130 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19118 eq19120
    | exact resolve eq19120 eq19118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19120
  have eq19200 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq19118 eq660
    | exact resolve eq660 eq19118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660 eq19118
  have eq19215 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq181 eq19200
    | exact resolve eq19200 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq19200
  have eq19223 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19074 eq19215
    | exact resolve eq19215 eq19074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19074 eq19215
  have eq19230 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19130 eq19223
    | exact resolve eq19223 eq19130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19223
  have eq19234 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19130 eq19230
    | exact resolve eq19230 eq19130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19130 eq19230
  have eq21205 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq808 x
       have i₂ := eq902
       grind)
    | exact superpose eq902 eq808
    | (have j0 := eq808 x
       grind)
    | exact resolve eq808 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq902
  have eq21316 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21205
       have i₂ := eq18736
       grind)
    | exact superpose eq18736 eq21205
    | exact resolve eq21205 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21205
  have eq21338 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18755 eq21316
    | exact resolve eq21316 eq18755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21316
  have eq21349 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq21338
       have i₂ := eq18736
       grind)
    | exact superpose eq18736 eq21338
    | exact resolve eq21338 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21338
  have eq21350 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq21349
  have eq21353 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq21350
       have i₂ := eq18736
       grind)
    | exact superpose eq18736 eq21350
    | exact resolve eq21350 eq18736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18736 eq21350
  have eq21549 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21353 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq21353
       grind)
    | exact resolve eq13 eq21353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21569 : y ≠ (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq21353
  have eq21570 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq21549
  have eq21601 : y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq21570 eq18765
    | exact resolve eq18765 eq21570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18765 eq21570
  have eq21612 : y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq21601
  have eq21629 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq21612
       have r₂ := eq21569
       grind)
    | exact resolve eq21612 eq21569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21569 eq21612
  have eq21683 : y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq21629 eq18759
    | exact resolve eq18759 eq21629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18759 eq21629
  have eq21725 : y = (M.op x y) := by
    first
    | exact superpose eq18755 eq21683
    | exact resolve eq21683 eq18755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18755 eq21683
  have eq21745 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq21725
       grind)
    | exact superpose eq21725 eq24
    | exact resolve eq24 eq21725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq21725
  have eq21812 : (σ x) = (σ y) := by
    first
    | exact superpose eq18756 eq21745
    | exact resolve eq21745 eq18756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18756 eq21745
  have eq21930 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21812 eq19234
    | exact resolve eq19234 eq21812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19234
  have eq21951 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19043 eq21930
    | exact resolve eq21930 eq19043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19043 eq21930
  have eq21984 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21812 eq21951
    | exact resolve eq21951 eq21812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21812 eq21951
  have eq21985 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21984
  have eq22007 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq21985 eq27
    | exact resolve eq27 eq21985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21985
  have eq22078 : False := by grind
  exact eq22078

/-- `Equation4438`: `x ◇ (y ◇ x) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_y_pyx_x_pyx_Equation4438 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4438 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4438.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X0) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) X1)
       have r₂ := eq13 (M.op X0 X0) X1
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
  have eq177 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (M.op X0 X1) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 (M.op x X0)
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : x ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq662 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X2 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 y X0 x
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq669 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq182
    | (have j0 := eq182 (σ y) X0 (σ x)
       grind)
    | exact resolve eq182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq698 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq667 (M.op y x)
       have i₂ := eq16 y X0 x
       grind)
    | exact superpose eq16 eq667
    | exact resolve eq667 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq704 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op y X1) y) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq16 y x x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq16
    | (have j0 := eq16 y x X1
       grind)
    | exact resolve eq16 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : (M.op y (M.op x y)) = (M.op y (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq698 x
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq698 x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq698
    | (have j0 := eq698 x
       grind)
    | exact resolve eq698 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq720 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) (σ y)) := by
    intro X1
    first
    | exact superpose eq669 eq16
    | (have j0 := eq16 (σ y) (σ x) X1
       grind)
    | exact resolve eq16 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X1
       have r₂ := eq28 X0 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X0) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X1 := by
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
  have eq801 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (k X0 X1) X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq815 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq28 X0 (M.op X0 X1)
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 (M.op X0 X1)
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
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
  have eq831 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq838 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq840 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq853 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq822
       grind)
    | exact superpose eq822 eq40
    | exact resolve eq40 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq822
  have eq854 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq853
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq853
    | exact resolve eq853 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853
  have eq856 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq854
    | exact resolve eq854 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq863 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq838 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq838
    | (have j0 := eq838 (σ X0)
       grind)
    | exact resolve eq838 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq866 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq856 eq831
    | exact resolve eq831 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq873 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq866
       have r₂ := eq27
       grind)
    | exact resolve eq866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq878 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq873 eq720
    | exact resolve eq720 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq879 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq873 eq669
    | exact resolve eq669 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq880 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ y) = (M.op (σ y) X0) ∨ (σ y) = (k (σ y) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq873 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq873
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq873
       grind)
    | exact resolve eq12 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq873 eq13
    | exact resolve eq13 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq873 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq893 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq881
       have r₂ := eq883
       grind)
    | exact resolve eq881 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881 eq883
  have eq894 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq878
    | exact resolve eq878 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq899 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq893 eq116
    | exact resolve eq116 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq906 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq899
    | exact resolve eq899 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq899
  have eq911 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq894 eq720
    | exact resolve eq720 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq916 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq894 eq177
    | exact resolve eq177 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq720 eq916
    | exact resolve eq916 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq916
  have eq922 : (M.op (σ y) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq879 eq919
    | exact resolve eq919 eq879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq879 eq919
  have eq925 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq911 eq922
    | exact resolve eq922 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq922
  have eq950 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq925 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq950
    | exact resolve eq950 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq967 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq856 eq962
    | exact resolve eq962 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq972 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq967
       have r₂ := eq27
       grind)
    | exact resolve eq967 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq1493 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq880 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq1494 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq856 eq1493
    | exact resolve eq1493 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq1493
  have eq1498 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1494 eq925
    | exact resolve eq925 eq1494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925 eq1494
  have eq1511 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1498
  have eq1524 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1511
       have r₂ := eq972
       grind)
    | exact resolve eq1511 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq1534 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq704 y
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq704
    | exact resolve eq704 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1535 : (M.op y x) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq667 y
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq667
    | exact resolve eq667 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1537 : x ≠ y ∨ x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq13
    | exact resolve eq13 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1539 : x = (k y y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq28
    | exact resolve eq28 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1543 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq178 y y X0
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq178
    | exact resolve eq178 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1548 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1543 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1543
    | (have j0 := eq1543 X0
       grind)
    | exact resolve eq1543 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1543
  have eq1553 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq1537
       have r₂ := eq1539
       grind)
    | exact resolve eq1537 eq1539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537 eq1539
  have eq1554 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1534
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1534
    | exact resolve eq1534 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1556 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1548 x
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq1548 x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq1548
    | (have j0 := eq1548 x
       grind)
    | exact resolve eq1548 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1561 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1554 eq1556
    | exact resolve eq1556 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556
  have eq1563 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq1553
       grind)
    | exact superpose eq1553 eq41
    | exact resolve eq41 eq1553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1566 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1563
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1563
    | exact resolve eq1563 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1563
  have eq1568 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1566
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1566
    | exact resolve eq1566 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1566
  have eq1593 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1561 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq1561
       grind)
    | exact resolve eq13 eq1561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq1602 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1593
  have eq1604 : (M.op x y) = (k (M.op x y) y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1554 eq1602
    | exact resolve eq1602 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1602
  have eq1608 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1568 eq838
    | (have j0 := eq838 (σ y)
       grind)
    | exact resolve eq838 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1615 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1604 eq41
    | exact resolve eq41 eq1604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1616 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq1615
    | exact resolve eq1615 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1615
  have eq1833 : (σ y) = (k (σ y) (σ (M.op y y))) ∨ y = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq37 (M.op y y)
       have i₂ := eq840 y
       grind)
    | exact superpose eq840 eq37
    | (have j1 := eq840 y
       grind)
    | exact resolve eq37 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1842 : (σ y) = (k (σ y) (σ (M.op y y))) ∨ y = (M.op y (M.op y y)) := by
    first
    | (have i₁ := eq1833
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1833
    | exact resolve eq1833 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1833
  have eq1849 : (σ y) = (k (σ y) (σ (M.op y y))) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1842
       have i₂ := eq667 y
       grind)
    | exact superpose eq667 eq1842
    | exact resolve eq1842 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq2140 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq801 y y X0
       have i₂ := eq906
       grind)
    | exact superpose eq906 eq801
    | (have j0 := eq801 y y x
       grind)
    | exact resolve eq801 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2235 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2140 x
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq2140 x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq2140
    | (have j0 := eq2140 x
       grind)
    | exact resolve eq2140 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2140
  have eq2254 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2235
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2235
    | exact resolve eq2235 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235
  have eq2388 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2254 eq704
    | exact resolve eq704 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2418 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2388 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq2388
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq2388
       grind)
    | exact resolve eq13 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388
  have eq2428 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq2418
  have eq2434 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2254 eq2428
    | exact resolve eq2428 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254 eq2428
  have eq2440 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq2434 eq41
    | exact resolve eq41 eq2434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2434
  have eq2443 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq2440
    | exact resolve eq2440 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2440
  have eq2446 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1524 eq2443
    | exact resolve eq2443 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2443
  have eq2449 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq893 eq2446
    | exact resolve eq2446 eq893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893 eq2446
  have eq2452 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2449
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq2449
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq2449 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2458 : y ≠ y ∨ y = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2449
       grind)
    | exact superpose eq2449 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq2449
       grind)
    | exact resolve eq13 eq2449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2467 : x ≠ y ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq2449
  have eq2468 : y = (k y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq2458
  have eq2475 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq906 eq2468
    | exact resolve eq2468 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468
  have eq2479 : (σ x) = (σ y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq838 y
       grind)
    | (have r₁ := eq2452
       have r₂ := eq838 y
       grind)
    | exact resolve eq2452 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq2452
  have eq2485 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2475
       have r₂ := eq2467
       grind)
    | exact resolve eq2475 eq2467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2467 eq2475
  have eq2486 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq906 eq2479
    | exact resolve eq2479 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2489 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq704 y
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq704
    | exact resolve eq704 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2490 : (M.op y x) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq667 y
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq667
    | exact resolve eq667 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2493 : x ≠ y ∨ x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq13
    | exact resolve eq13 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2499 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq178 y y X0
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq178
    | exact resolve eq178 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2507 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq2499 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2499
    | (have j0 := eq2499 X0
       grind)
    | exact resolve eq2499 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2499
  have eq2512 : x = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq2493
       have r₂ := eq2486
       grind)
    | exact resolve eq2493 eq2486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486 eq2493
  have eq2513 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2489
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2489
    | exact resolve eq2489 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2489
  have eq2515 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2507 x
       have i₂ := eq667 x
       grind)
    | (have i₁ := eq2507 x
       have i₂ := eq667 x
       grind)
    | exact superpose eq667 eq2507
    | (have j0 := eq2507 x
       grind)
    | exact resolve eq2507 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667 eq2507
  have eq2520 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2513 eq2515
    | exact resolve eq2515 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515
  have eq2523 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2512
       grind)
    | exact superpose eq2512 eq41
    | exact resolve eq41 eq2512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2512
  have eq2528 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2523
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2523
    | exact resolve eq2523 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2523
  have eq2531 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2528
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2528
    | exact resolve eq2528 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2528
  have eq2559 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2520 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq2520
       grind)
    | exact resolve eq13 eq2520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2520
  have eq2569 : (k (M.op x y) y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq2559
  have eq2571 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2513 eq2569
    | exact resolve eq2569 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569
  have eq2577 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2531 eq801
    | (have j0 := eq801 (σ y) (σ y) x
       grind)
    | exact resolve eq801 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2579 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq669 eq2577
    | (have j0 := eq2577 (σ x)
       grind)
    | exact resolve eq2577 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2577
  have eq2583 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq2579
    | exact resolve eq2579 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579
  have eq2587 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2571 eq41
    | exact resolve eq41 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571
  have eq2590 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq2587
    | exact resolve eq2587 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2587
  have eq3558 : ∀ X0 : G, (M.op y x) = (k y (M.op y X0)) ∨ x = (M.op y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq815 y x y
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq815
    | exact resolve eq815 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3560 : ∀ X0 : G, (M.op y x) = (k y (M.op y X0)) ∨ x = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq815 y x y
       have i₂ := eq1524
       grind)
    | exact superpose eq1524 eq815
    | exact resolve eq815 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq815 eq1524
  have eq3724 : ∀ X0 : G, (M.op y (M.op x y)) = (k y (M.op y X0)) ∨ x = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1535 eq3560
    | (have j0 := eq3560 X0
       grind)
    | exact resolve eq3560 eq1535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535 eq3560
  have eq3725 : ∀ X0 : G, (M.op y (M.op x y)) = (k y (M.op y X0)) ∨ x = (M.op y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2490 eq3558
    | (have j0 := eq3558 X0
       grind)
    | exact resolve eq3558 eq2490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2490 eq3558
  have eq3747 : ∀ X0 : G, (M.op x y) = (k y (M.op y X0)) ∨ x = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq1554 eq3724
    | (have j0 := eq3724 X0
       grind)
    | exact resolve eq3724 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq3748 : ∀ X0 : G, (M.op x y) = (k y (M.op y X0)) ∨ x = (M.op y X0) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2513 eq3725
    | (have j0 := eq3725 X0
       grind)
    | exact resolve eq3725 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq7355 : (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1554 eq3747
    | exact resolve eq3747 eq1554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1554 eq3747
  have eq7387 : (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq7355
  have eq7418 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7387 eq37
    | exact resolve eq37 eq7387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7387
  have eq7428 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq7418
    | exact resolve eq7418 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7418
  have eq7434 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7428 eq799
    | (have j0 := eq799 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq799 (σ y) (σ (M.op x y))
       have r₂ := eq7428
       grind)
    | exact resolve eq799 eq7428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7436 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq7434
  have eq7437 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1616 eq7436
    | exact resolve eq7436 eq1616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616 eq7436
  have eq7702 : (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2513 eq3748
    | exact resolve eq3748 eq2513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2513 eq3748
  have eq7732 : (M.op x y) = (k y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq7702
  have eq7765 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7732 eq37
    | exact resolve eq37 eq7732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq7732
  have eq7775 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq7765
    | exact resolve eq7765 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7765
  have eq7781 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7775 eq799
    | (have j0 := eq799 (σ y) (σ (M.op x y))
       grind)
    | (have r₁ := eq799 (σ y) (σ (M.op x y))
       have r₂ := eq7775
       grind)
    | exact resolve eq799 eq7775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq7783 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq7781
  have eq7784 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2590 eq7783
    | exact resolve eq7783 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590 eq7783
  have eq10584 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7437 eq669
    | exact resolve eq669 eq7437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10585 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7437 eq840
    | exact resolve eq840 eq7437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10589 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7437 eq28
    | exact resolve eq28 eq7437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10602 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq7437 eq662
    | exact resolve eq662 eq7437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq10606 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq10589
  have eq10612 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq669 eq10602
    | (have j0 := eq10602 (σ x)
       grind)
    | exact resolve eq10602 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10602
  have eq10623 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1568 eq10606
    | exact resolve eq10606 eq1568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1568 eq10606
  have eq10625 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7428 eq10585
    | exact resolve eq10585 eq7428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10585
  have eq10626 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq10625
  have eq10634 : (M.op (σ y) (σ (M.op x y))) = (M.op (σ y) (M.op (σ y) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10584 eq10612
    | exact resolve eq10612 eq10584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10584 eq10612
  have eq10643 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10623 eq10626
    | exact resolve eq10626 eq10623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10626
  have eq10646 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ y) (σ x))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10623 eq10634
    | exact resolve eq10634 eq10623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10623 eq10634
  have eq10656 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10643 eq10646
    | exact resolve eq10646 eq10643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10643 eq10646
  have eq11156 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq10656 eq7437
    | exact resolve eq7437 eq10656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7437 eq10656
  have eq11185 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq11156
  have eq11205 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11185 eq720
    | exact resolve eq720 eq11185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11240 : (k (σ y) (σ (M.op x y))) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11205 eq28
    | (have j0 := eq28 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq28 eq11205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11272 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7428 eq11240
    | exact resolve eq11240 eq7428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11240
  have eq12708 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7784 eq720
    | exact resolve eq720 eq7784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7784
  have eq12760 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq11205 eq12708
    | exact resolve eq12708 eq11205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12708
  have eq12797 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2583 eq12760
    | exact resolve eq12760 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583 eq12760
  have eq13234 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11272 eq720
    | exact resolve eq720 eq11272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11272
  have eq13850 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13234 eq840
    | exact resolve eq840 eq13234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq13234
  have eq13899 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7428 eq13850
    | exact resolve eq13850 eq7428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7428 eq13850
  have eq13900 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13899
  have eq13924 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11185 eq13900
    | exact resolve eq13900 eq11185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11185 eq13900
  have eq13925 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq13924
  have eq13962 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13925 eq11205
    | exact resolve eq11205 eq13925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11205
  have eq13963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13925 eq12797
    | exact resolve eq12797 eq13925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12797 eq13925
  have eq13987 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq13963
  have eq13988 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq13962
  have eq14008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq13987
       have r₂ := eq1608
       grind)
    | exact resolve eq13987 eq1608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608 eq13987
  have eq14016 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq14008
       have r₂ := eq27
       grind)
    | exact resolve eq14008 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14008
  have eq14153 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14016 eq669
    | exact resolve eq669 eq14016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14203 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13988 eq14153
    | exact resolve eq14153 eq13988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13988 eq14153
  have eq14217 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14016 eq14203
    | exact resolve eq14203 eq14016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14016 eq14203
  have eq14218 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq14217
  have eq14232 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14218 eq29
    | exact resolve eq29 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq14252 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14218 eq7775
    | exact resolve eq7775 eq14218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7775 eq14218
  have eq14273 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq14252
  have eq14279 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2531 eq14273
    | exact resolve eq14273 eq2531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2531 eq14273
  have eq14280 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq14279
  have eq14301 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq14232
    | exact resolve eq14232 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14232
  have eq14311 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14280 eq32
    | exact resolve eq32 eq14280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14280
  have eq14542 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq14311
    | exact resolve eq14311 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq14311
  have eq14589 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14301 eq14542
    | exact resolve eq14542 eq14301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14301 eq14542
  have eq14590 : x = (M.op x y) := by grind
  clear eq14589
  have eq14604 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq14590
       grind)
    | exact superpose eq14590 eq18
    | exact resolve eq18 eq14590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq14605 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq14590
       grind)
    | exact superpose eq14590 eq22
    | exact resolve eq22 eq14590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14609 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq185
       have i₂ := eq14590
       grind)
    | exact superpose eq14590 eq185
    | (have r₁ := eq185
       have r₂ := eq14590
       grind)
    | exact resolve eq185 eq14590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq14651 : (k (M.op x y) y) = (M.op y (M.op x y)) := by grind
  clear eq14609
  have eq14665 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq14605 eq20
    | exact resolve eq20 eq14605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14814 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) X0)) ∨ (M.op (M.op x y) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq14604 eq800
    | (have j0 := eq800 (M.op x y) (M.op (M.op x y) (k (M.op x y) X0)) x
       grind)
    | exact resolve eq800 eq14604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq14972 : (k (M.op x y) y) = (M.op y (k (M.op x y) y)) := by
    first
    | exact superpose eq14651 eq711
    | exact resolve eq711 eq14651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq14985 : (k (M.op x y) y) = (M.op (k (M.op x y) y) y) := by
    first
    | exact superpose eq14651 eq704
    | exact resolve eq704 eq14651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq16064 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op (k (M.op x y) y) y) := by
    intro X0
    first
    | exact superpose eq14972 eq177
    | exact resolve eq177 eq14972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq14972
  have eq16084 : ∀ X0 : G, (k (M.op x y) y) = (M.op (M.op y X0) y) := by
    intro X0
    first
    | exact superpose eq14985 eq16064
    | exact resolve eq16064 eq14985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14985 eq16064
  have eq27169 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq863 y
       have i₂ := eq906
       grind)
    | exact superpose eq906 eq863
    | (have j0 := eq863 y
       grind)
    | exact resolve eq863 eq906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq27290 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27169
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27169
    | exact resolve eq27169 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27169
  have eq27332 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27290
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27290
    | exact resolve eq27290 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq27290
  have eq27355 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq27332
       have r₂ := eq2485
       grind)
    | exact resolve eq27332 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485 eq27332
  have eq27370 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27355
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27355
    | exact resolve eq27355 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27355
  have eq27380 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq27370
       have i₂ := eq14590
       grind)
    | exact superpose eq14590 eq27370
    | exact resolve eq27370 eq14590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27370
  have eq27429 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27380 eq669
    | exact resolve eq669 eq27380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27472 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27380 eq27429
    | exact resolve eq27429 eq27380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27380 eq27429
  have eq27708 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq27472 eq894
    | exact resolve eq894 eq27472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq27472
  have eq27810 : x = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq27708
       have r₂ := eq972
       grind)
    | exact resolve eq27708 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972 eq27708
  have eq27843 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq27810
       have i₂ := eq14590
       grind)
    | exact superpose eq14590 eq27810
    | exact resolve eq27810 eq14590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27810
  have eq27844 : (M.op x y) = (M.op y y) := by grind
  clear eq27843
  have eq27871 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1849
       have i₂ := eq27844
       grind)
    | exact superpose eq27844 eq1849
    | exact resolve eq1849 eq27844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849
  have eq27877 : (k (M.op x y) y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq16084 y
       have i₂ := eq27844
       grind)
    | exact superpose eq27844 eq16084
    | exact resolve eq16084 eq27844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16084
  have eq27886 : y ≠ (M.op x y) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq27844
       grind)
    | exact superpose eq27844 eq13
    | exact resolve eq13 eq27844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27888 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq27844
       grind)
    | exact superpose eq27844 eq28
    | exact resolve eq28 eq27844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27844
  have eq27918 : (M.op x y) = (k y y) := by
    first
    | (have r₁ := eq27886
       have r₂ := eq27888
       grind)
    | exact resolve eq27886 eq27888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27886 eq27888
  have eq27921 : (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq14604 eq27877
    | exact resolve eq27877 eq14604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27877
  have eq27922 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20 eq27871
    | exact resolve eq27871 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27871
  have eq27927 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq14665 eq27922
    | exact resolve eq27922 eq14665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27922
  have eq27929 : y = (k (M.op x y) y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq14651 eq27927
    | exact resolve eq27927 eq14651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14651 eq27927
  have eq27930 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27921 eq27929
    | exact resolve eq27929 eq27921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27929
  have eq27965 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq27918
       grind)
    | exact superpose eq27918 eq41
    | exact resolve eq41 eq27918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27966 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq863 y
       have i₂ := eq27918
       grind)
    | exact superpose eq27918 eq863
    | (have j0 := eq863 y
       grind)
    | exact resolve eq863 eq27918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863 eq27918
  have eq27973 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq27966
    | exact resolve eq27966 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27966
  have eq27974 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq27965
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27965
    | exact resolve eq27965 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27965
  have eq27977 : (σ y) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq14665 eq27973
    | exact resolve eq27973 eq14665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27973
  have eq27978 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq27974
    | exact resolve eq27974 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27974
  have eq27980 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq27977
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27977
    | exact resolve eq27977 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27977
  have eq27981 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq14665 eq27978
    | exact resolve eq27978 eq14665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27978
  have eq27983 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq27980
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq27980
    | exact resolve eq27980 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27980
  have eq28046 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq27981 eq801
    | (have j0 := eq801 (σ y) (σ y) x
       grind)
    | exact resolve eq801 eq27981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq28047 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq669 eq28046
    | (have j0 := eq28046 (σ x)
       grind)
    | exact resolve eq28046 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28046
  have eq28051 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq28047
    | exact resolve eq28047 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28047
  have eq28068 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq27921 eq41
    | exact resolve eq41 eq27921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq27921
  have eq28073 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq28068
    | exact resolve eq28068 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq28068
  have eq28078 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq14665 eq28073
    | exact resolve eq28073 eq14665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28073
  have eq28494 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27930 eq831
    | exact resolve eq831 eq27930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831 eq27930
  have eq29054 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq28051 eq720
    | exact resolve eq720 eq28051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28051
  have eq32198 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28494 eq720
    | exact resolve eq720 eq28494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq32199 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28494 eq669
    | exact resolve eq669 eq28494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669 eq28494
  have eq32246 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq32198
    | exact resolve eq32198 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32198
  have eq33297 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32199 eq32246
    | exact resolve eq32246 eq32199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32199 eq32246
  have eq33328 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq33297
  have eq33390 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33328 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq33328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33328
  have eq33431 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28078 eq33390
    | exact resolve eq33390 eq28078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28078 eq33390
  have eq37328 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33431 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq33431
       grind)
    | exact resolve eq13 eq33431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37330 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33431 eq28
    | exact resolve eq28 eq33431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33431
  have eq37384 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq37328
       have r₂ := eq37330
       grind)
    | exact resolve eq37328 eq37330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37328 eq37330
  have eq37442 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37384 eq98
    | exact resolve eq98 eq37384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq37384
  have eq37483 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq37442
       have i₂ := eq14590
       grind)
    | exact superpose eq14590 eq37442
    | exact resolve eq37442 eq14590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14590 eq37442
  have eq37489 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq37483
    | exact resolve eq37483 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq37483
  have eq37620 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37489 eq14814
    | (have j0 := eq14814 (M.op (M.op x y) y)
       grind)
    | exact resolve eq14814 eq37489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14814
  have eq37648 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14604 eq37620
    | exact resolve eq37620 eq14604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14604 eq37620
  have eq37649 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37648
  have eq37800 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37649 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq37649
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq37649
       grind)
    | exact resolve eq13 eq37649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37649
  have eq37823 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37800
  have eq37855 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37823 eq37489
    | exact resolve eq37489 eq37823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37489 eq37823
  have eq37869 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37855
  have eq37976 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37869 eq29054
    | exact resolve eq29054 eq37869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29054
  have eq37985 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37869
  have eq37986 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq37976
  have eq38063 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq37986 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq37986
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq37986
       grind)
    | exact resolve eq13 eq37986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37986
  have eq38086 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq38063
  have eq38122 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27981 eq38086
    | exact resolve eq38086 eq27981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27981 eq38086
  have eq38139 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq38122
       have r₂ := eq37985
       grind)
    | exact resolve eq38122 eq37985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37985 eq38122
  have eq38148 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38139 eq27
    | exact resolve eq27 eq38139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38139
  have eq38347 : y = (M.op x y) := by
    first
    | (have r₁ := eq38148
       have r₂ := eq14665
       grind)
    | exact resolve eq38148 eq14665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38148
  have eq38371 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38347
       grind)
    | exact superpose eq38347 eq24
    | exact resolve eq24 eq38347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38347
  have eq38591 : (σ x) = (σ y) := by
    first
    | exact superpose eq14605 eq38371
    | exact resolve eq38371 eq14605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14605 eq38371
  have eq38609 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq38591 eq26
    | exact resolve eq26 eq38591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq38751 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq38591 eq27983
    | (have r₁ := eq27983
       have r₂ := eq38591
       grind)
    | exact resolve eq27983 eq38591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27983 eq38591
  have eq38774 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq38751
  have eq38839 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq38774 eq38609
    | exact resolve eq38609 eq38774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38609 eq38774
  have eq38868 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq38839 eq27
    | exact resolve eq27 eq38839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq38839
  have eq39040 : False := by grind
  exact eq39040

/-- `Equation4438`: `x ◇ (y ◇ x) = (x ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_y_x_pyx_Equation4438 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4438 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4438.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X0) := by
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
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
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
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
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
  have eq115 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq47 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 y
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
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
  have eq163 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq85
    | exact resolve eq85 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq174 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) (M.op X2 X0)) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 X0) X0 X3
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq16 X0 x X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X2) X3 X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op (M.op x y) x) := by
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
  have eq181 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X0 X2 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ x) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq39
    | exact resolve eq39 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq40
    | exact resolve eq40 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (σ y) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq184
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq184
    | exact resolve eq184 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq188 : (σ x) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq183
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq183
    | exact resolve eq183 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq197 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op x X1) x) := by
    intro X1
    first
    | (have i₁ := eq16 x x X1
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) X1) (σ x)) := by
    intro X1
    first
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq141
    | exact resolve eq141 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq260
    | exact resolve eq260 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq288 : (τ (σ y)) = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | (have i₁ := eq152 (M.op sF3 sF3)
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq152
    | exact resolve eq152 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : y = (k (τ (M.op (σ y) (σ y))) y) := by
    first
    | exact superpose eq31 eq288
    | exact resolve eq288 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq316 : (τ (σ (M.op x y))) = (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op x y)) := by
    first
    | (have i₁ := eq163 (M.op sF1 sF1)
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq163
    | exact resolve eq163 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq337 : (M.op x y) = (k (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) (M.op x y)) := by
    first
    | exact superpose eq28 eq316
    | exact resolve eq316 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq316
  have eq805 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq182 X0 X2 (M.op X0 x)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq182
    | exact resolve eq182 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq810 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq182 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 y X0 x
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq182
    | (have j0 := eq182 (σ y) X0 (σ x)
       grind)
    | exact resolve eq182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq847 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
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
  have eq849 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq863 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq869 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = (M.op (k X0 X1) X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq877 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op x (k x X0)) ∨ x = (M.op X0 x) ∨ x = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq11 x X0
       grind)
    | exact superpose eq11 eq180
    | (have j1 := eq11 x X0
       grind)
    | exact resolve eq180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq878 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (k (σ x) X0)) ∨ (σ x) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 X0) := by
    intro X0
    first
    | (have i₁ := eq181 x
       have i₂ := eq11 sF2 x
       grind)
    | exact superpose eq11 eq181
    | (have j1 := eq11 (σ x) X0
       grind)
    | exact resolve eq181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq881 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X2 X1
       have i₂ := eq11 X0 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 (M.op X0 X1)
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq903 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq904 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq903 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq944 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op y (M.op y (M.op X0 y))) := by
    intro X0
    first
    | (have i₁ := eq810 (M.op y x)
       have i₂ := eq16 y X0 x
       grind)
    | exact superpose eq16 eq810
    | exact resolve eq810 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op (M.op y X1) y) := by
    intro X1
    first
    | (have i₁ := eq16 y x X1
       have i₂ := eq810 x
       grind)
    | (have i₁ := eq16 y x x
       have i₂ := eq810 x
       grind)
    | exact superpose eq810 eq16
    | (have j0 := eq16 y x X1
       grind)
    | exact resolve eq16 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq960 : (M.op y (M.op x y)) = (M.op y (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq944 x
       have i₂ := eq810 x
       grind)
    | (have i₁ := eq944 x
       have i₂ := eq810 x
       grind)
    | exact superpose eq810 eq944
    | (have j0 := eq944 x
       grind)
    | exact resolve eq944 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq971 : ∀ X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) (σ y)) := by
    intro X1
    first
    | exact superpose eq812 eq16
    | (have j0 := eq16 (σ y) (σ x) X1
       grind)
    | exact resolve eq16 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq1053 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq904 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq904
    | (have j0 := eq904 (σ X0)
       grind)
    | exact resolve eq904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1417 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq861
       grind)
    | exact superpose eq861 eq39
    | exact resolve eq39 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1418 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1417
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1417
    | exact resolve eq1417 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq1420 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1418
    | exact resolve eq1418 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1678 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1420 eq863
    | exact resolve eq863 eq1420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1685 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq1678
       have r₂ := eq27
       grind)
    | exact resolve eq1678 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq1727 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1685
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq1685
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq1685 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1728 : x = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1685 eq281
    | exact resolve eq281 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1729 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1685 eq203
    | exact resolve eq203 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1730 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1685 eq181
    | exact resolve eq181 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1733 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1685 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1743 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1685 eq805
    | exact resolve eq805 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1744 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq1733
  have eq1745 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1727
  have eq1746 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq26 eq1743
    | (have j0 := eq1743 X0
       grind)
    | exact resolve eq1743 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1755 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq1730
    | exact resolve eq1730 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1730
  have eq1756 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq1728
    | exact resolve eq1728 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq1757 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq181 eq1746
    | exact resolve eq1746 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1746
  have eq1763 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1756
       have r₂ := eq13 y x
       grind)
    | exact resolve eq1756 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1756
  have eq1764 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1755 eq1757
    | exact resolve eq1757 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1767 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq861
       have i₂ := eq1763
       grind)
    | exact superpose eq1763 eq861
    | exact resolve eq861 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1768 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq1763
       grind)
    | exact superpose eq1763 eq36
    | exact resolve eq36 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1771 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1767
  have eq1776 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1768
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1768
    | exact resolve eq1768 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1768
  have eq1782 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1776 eq863
    | exact resolve eq863 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1787 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1782
  have eq1799 : (M.op (M.op x y) x) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq197 x
       have i₂ := eq1771
       grind)
    | exact superpose eq1771 eq197
    | exact resolve eq197 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1800 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq1771
       grind)
    | exact superpose eq1771 eq180
    | exact resolve eq180 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1803 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq1771
       grind)
    | exact superpose eq1771 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1814 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1803
  have eq1825 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1800
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1800
    | exact resolve eq1800 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1835 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1787
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq1787
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq1787 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1837 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1787 eq203
    | exact resolve eq203 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1838 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1787 eq181
    | exact resolve eq181 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1841 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1787 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1851 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1787 eq805
    | exact resolve eq805 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1852 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1841
  have eq1853 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1835
  have eq1854 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq1851
    | (have j0 := eq1851 X0
       grind)
    | exact resolve eq1851 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1851
  have eq1863 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1838
    | exact resolve eq1838 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq1865 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq181 eq1854
    | exact resolve eq1854 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1854
  have eq1871 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1863 eq1865
    | exact resolve eq1865 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq1914 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1825 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1925 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1914
  have eq1930 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq1925
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq1925 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1925
  have eq1966 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1863 eq805
    | exact resolve eq805 eq1863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1968 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq181 eq1966
    | exact resolve eq1966 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1966
  have eq1974 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1837 eq1968
    | exact resolve eq1968 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1968
  have eq1978 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1871 eq1974
    | exact resolve eq1974 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1974
  have eq1980 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1871 eq1978
    | exact resolve eq1978 eq1871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1871 eq1978
  have eq2041 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1930 eq35
    | exact resolve eq35 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq2045 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2041
    | exact resolve eq2041 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2041
  have eq2052 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1980 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq1980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2063 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2052
  have eq2124 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq1755 eq805
    | exact resolve eq805 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq2125 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq181 eq2124
    | exact resolve eq2124 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq2131 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1729 eq2125
    | exact resolve eq2125 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729 eq2125
  have eq2136 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1764 eq2131
    | exact resolve eq2131 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq2138 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1764 eq2136
    | exact resolve eq2136 eq1764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764 eq2136
  have eq2158 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2138 eq971
    | exact resolve eq971 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2193 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq951 x
       have i₂ := eq1799
       grind)
    | exact superpose eq1799 eq951
    | exact resolve eq951 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2195 : (k x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq1799
       grind)
    | exact superpose eq1799 eq11
    | (have j0 := eq11 x (M.op x y)
       grind)
    | exact resolve eq11 eq1799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq2212 : (M.op x y) = (k x y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1825 eq2195
    | exact resolve eq2195 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2213 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1825 eq2193
    | exact resolve eq2193 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2220 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1825 eq2212
    | exact resolve eq2212 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2212
  have eq2221 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2220
  have eq2367 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X0 X2)) = (M.op (M.op X0 X2) (M.op (M.op X2 X3) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq175 X2 X3 X0 X0
       have i₂ := eq177 X0 X2 X1
       grind)
    | (have i₁ := eq175 X2 X3 X0 X0
       have i₂ := eq177 X0 X1 X2
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2869 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq1814
       grind)
    | exact superpose eq1814 eq39
    | exact resolve eq39 eq1814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq2875 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2869
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2869
    | exact resolve eq2869 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2869
  have eq2877 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2875
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2875
    | exact resolve eq2875 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2875
  have eq3044 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1852 eq97
    | exact resolve eq97 eq1852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1852
  have eq3054 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq3044
    | exact resolve eq3044 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044
  have eq3775 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1744 eq97
    | exact resolve eq97 eq1744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq3785 : y = (k x x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq3775
    | exact resolve eq3775 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3775
  have eq3788 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1771 eq3785
    | exact resolve eq3785 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3785
  have eq3893 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2877 eq869
    | (have j0 := eq869 (σ x) (σ x) x
       grind)
    | exact resolve eq869 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3976 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3893 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3893
  have eq4001 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq181 eq3976
    | exact resolve eq3976 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq4149 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1853 eq97
    | exact resolve eq97 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853
  have eq4166 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq31 eq4149
    | exact resolve eq4149 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149
  have eq4198 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2221
       grind)
    | exact superpose eq2221 eq40
    | exact resolve eq40 eq2221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4204 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4198
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4198
    | exact resolve eq4198 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4198
  have eq4206 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4204
    | exact resolve eq4204 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204
  have eq4254 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq4166 eq181
    | exact resolve eq181 eq4166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166
  have eq4284 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq1787 eq4254
    | exact resolve eq4254 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4254
  have eq4296 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq3054 eq4284
    | exact resolve eq4284 eq3054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3054 eq4284
  have eq4349 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2063 eq4206
    | exact resolve eq4206 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4206
  have eq4357 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq4349
  have eq4362 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4357
       have r₂ := eq27
       grind)
    | exact resolve eq4357 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4357
  have eq4460 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq4296 eq1863
    | exact resolve eq1863 eq4296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4296
  have eq4481 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4460
  have eq5606 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1745 eq97
    | exact resolve eq97 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq5629 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31 eq5606
    | exact resolve eq5606 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5606
  have eq5633 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1771 eq5629
    | exact resolve eq5629 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5629
  have eq5666 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5633 eq181
    | exact resolve eq181 eq5633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5633
  have eq5702 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1685 eq5666
    | exact resolve eq5666 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5666
  have eq5715 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq3788 eq5702
    | exact resolve eq5702 eq3788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3788 eq5702
  have eq5832 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5715 eq1863
    | exact resolve eq1863 eq5715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5715
  have eq5857 : y = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5832
  have eq6783 : y = (k (τ (σ x)) y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4362 eq309
    | exact resolve eq309 eq4362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq4362
  have eq6832 : y = (k x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq6783
    | exact resolve eq6783 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6783
  have eq6849 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq6832
       have r₂ := eq13 x y
       grind)
    | exact resolve eq6832 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6832
  have eq6859 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2221
       have i₂ := eq6849
       grind)
    | exact superpose eq6849 eq2221
    | exact resolve eq2221 eq6849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2221
  have eq6860 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq6849
       grind)
    | exact superpose eq6849 eq35
    | exact resolve eq35 eq6849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6849
  have eq6864 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6859
  have eq6871 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6860
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6860
    | exact resolve eq6860 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6860
  have eq6875 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq951 y
       have i₂ := eq6864
       grind)
    | exact superpose eq6864 eq951
    | exact resolve eq951 eq6864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6882 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op x (M.op (M.op y X1) y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq175 y X1 y x
       have i₂ := eq6864
       grind)
    | exact superpose eq6864 eq175
    | exact resolve eq175 eq6864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6919 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op x (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6882 X0 x
       have i₂ := eq951 x
       grind)
    | exact superpose eq951 eq6882
    | exact resolve eq6882 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6882
  have eq6922 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6875
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6875
    | exact resolve eq6875 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6875
  have eq6940 : (M.op (M.op x y) x) = (M.op x (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6919 x
       have i₂ := eq197 x
       grind)
    | (have i₁ := eq6919 y
       have i₂ := eq197 x
       grind)
    | exact superpose eq197 eq6919
    | (have j0 := eq6919 y
       grind)
    | exact resolve eq6919 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6919
  have eq6950 : (M.op x y) = (M.op x (M.op y (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1825 eq6940
    | exact resolve eq6940 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6940
  have eq6957 : (M.op x y) = (M.op x (M.op (M.op x y) y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2213 eq6950
    | exact resolve eq6950 eq2213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213 eq6950
  have eq6960 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6871 eq2063
    | exact resolve eq2063 eq6871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063 eq6871
  have eq6968 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6960
  have eq6984 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6922 eq951
    | exact resolve eq951 eq6922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6985 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6922 eq12
    | (have j0 := eq12 (M.op x y) y
       grind)
    | (have r₁ := eq12 (M.op x y) y
       have r₂ := eq6922
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6922
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6922
       grind)
    | exact resolve eq12 eq6922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6922
  have eq7005 : (M.op x y) = (k (M.op x y) y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq6985
  have eq7031 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6968 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq6968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6968
  have eq7052 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq7031
  have eq7367 : (M.op x y) ≠ (M.op (M.op x y) y) ∨ (M.op x x) = (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6957 eq12
    | (have j0 := eq12 (M.op (M.op x y) y) x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6957
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6957
       grind)
    | exact resolve eq12 eq6957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6957
  have eq7408 : (M.op x x) = (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7367
       have r₂ := eq6984
       grind)
    | exact resolve eq7367 eq6984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7367
  have eq7422 : y = (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1771 eq7408
    | exact resolve eq7408 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7408
  have eq7433 : y = (M.op x y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6984 eq7422
    | exact resolve eq7422 eq6984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7422
  have eq7434 : y = (M.op x y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7433
  have eq7439 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6984 eq7434
    | exact resolve eq7434 eq6984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6984 eq7434
  have eq7448 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7439 eq39
    | exact resolve eq39 eq7439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7439
  have eq7452 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq7448
    | exact resolve eq7448 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7448
  have eq7459 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7452 eq902
    | (have j0 := eq902 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq902 (σ x) (σ (M.op x y))
       have r₂ := eq7452
       grind)
    | exact resolve eq902 eq7452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7452
  have eq7460 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7459
  have eq7461 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1787 eq7460
    | exact resolve eq7460 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7460
  have eq7565 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7461 eq203
    | exact resolve eq203 eq7461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7576 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7461 eq182
    | exact resolve eq182 eq7461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7461
  have eq7597 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1837 eq7565
    | exact resolve eq7565 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7565
  have eq7606 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1980 eq7597
    | exact resolve eq7597 eq1980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7597
  have eq7621 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7606 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq7606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7606
  have eq7642 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7621
  have eq7662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2045 eq7642
    | exact resolve eq7642 eq2045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045 eq7642
  have eq7676 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7662
       have r₂ := eq27
       grind)
    | exact resolve eq7662 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7662
  have eq7774 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ (M.op x y)) (M.op X1 (σ (M.op x y)))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq7676 eq179
    | exact resolve eq179 eq7676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7799 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ (M.op x y)) (M.op X1 (σ (M.op x y)))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq181 eq7774
    | exact resolve eq7774 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7774
  have eq7814 : ∀ X1 : G, (M.op (σ y) (σ x)) = (M.op (M.op (σ (M.op x y)) (M.op X1 (σ (M.op x y)))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq1837 eq7799
    | exact resolve eq7799 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837 eq7799
  have eq7822 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (M.op X1 (σ (M.op x y)))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq1980 eq7814
    | exact resolve eq7814 eq1980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980 eq7814
  have eq7825 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7576 eq7822
    | exact resolve eq7822 eq7576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7576 eq7822
  have eq7827 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7676 eq7825
    | exact resolve eq7825 eq7676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7676 eq7825
  have eq7829 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1787 eq7827
    | exact resolve eq7827 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7827
  have eq7830 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq7829
  have eq8047 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7005 eq40
    | exact resolve eq40 eq7005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005
  have eq8053 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8047
    | exact resolve eq8047 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8047
  have eq8055 : (σ y) = (k (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7830 eq8053
    | exact resolve eq8053 eq7830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7830 eq8053
  have eq8140 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8055 eq7052
    | exact resolve eq7052 eq8055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7052
  have eq8145 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8055 eq152
    | exact resolve eq152 eq8055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq8055
  have eq8158 : (M.op x y) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq8140
  have eq8168 : (M.op x y) = (M.op y y) ∨ y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq8145
    | exact resolve eq8145 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8145
  have eq8181 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6864
       have i₂ := eq8158
       grind)
    | exact superpose eq8158 eq6864
    | exact resolve eq6864 eq8158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8158
  have eq8209 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq8181
  have eq8403 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6864
       have i₂ := eq8168
       grind)
    | exact superpose eq8168 eq6864
    | exact resolve eq6864 eq8168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6864 eq8168
  have eq8431 : y = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8403
  have eq8460 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq8431
       grind)
    | exact superpose eq8431 eq40
    | exact resolve eq40 eq8431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq8431
  have eq8483 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8460
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8460
    | exact resolve eq8460 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460
  have eq8486 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8209 eq8483
    | exact resolve eq8483 eq8209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8483
  have eq8524 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8486 eq902
    | (have j0 := eq902 (σ x) (σ x)
       grind)
    | (have r₁ := eq902 (σ x) (σ x)
       have r₂ := eq8486
       grind)
    | exact resolve eq902 eq8486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8486
  have eq8525 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8524
  have eq8526 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8525
  have eq8564 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8526 eq181
    | exact resolve eq181 eq8526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8604 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1787 eq8564
    | exact resolve eq8564 eq1787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1787 eq8564
  have eq8620 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8209 eq8604
    | exact resolve eq8604 eq8209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8209 eq8604
  have eq8768 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8620 eq1863
    | exact resolve eq1863 eq8620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1863 eq8620
  have eq8795 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8768
  have eq8821 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8795 eq27
    | exact resolve eq27 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8823 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8795 eq849
    | (have r₁ := eq849
       have r₂ := eq8795
       grind)
    | exact resolve eq849 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8825 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  have eq8826 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8823
  have eq8986 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8826 eq1420
    | exact resolve eq1420 eq8826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8997 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8986
  have eq9009 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8997
       have r₂ := eq8821
       grind)
    | exact resolve eq8997 eq8821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8997
  have eq9013 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1771 eq9009
    | exact resolve eq9009 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771 eq9009
  have eq9125 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9013 eq281
    | exact resolve eq281 eq9013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9013
  have eq9186 : x = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq9125
    | exact resolve eq9125 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9125
  have eq9201 : x = (k y x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq9186
       have r₂ := eq13 y x
       grind)
    | exact resolve eq9186 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9186
  have eq9222 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq861
       have i₂ := eq9201
       grind)
    | exact superpose eq9201 eq861
    | exact resolve eq861 eq9201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9223 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq9201
       grind)
    | exact superpose eq9201 eq36
    | exact resolve eq36 eq9201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9201
  have eq9227 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq9222
  have eq9233 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9223
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9223
    | exact resolve eq9223 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9223
  have eq9239 : (M.op (M.op x y) x) = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq197 x
       have i₂ := eq9227
       grind)
    | exact superpose eq9227 eq197
    | exact resolve eq197 eq9227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9240 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq9227
       grind)
    | exact superpose eq9227 eq180
    | exact resolve eq180 eq9227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9242 : ∀ X0 : G, y ≠ X0 ∨ x = (k X0 x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq9227
       grind)
    | exact superpose eq9227 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9227
       grind)
    | exact resolve eq13 eq9227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9243 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq9227
       grind)
    | exact superpose eq9227 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq9227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9264 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq9243
  have eq9285 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9240
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9240
    | exact resolve eq9240 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9240
  have eq9315 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9233 eq8826
    | exact resolve eq8826 eq9233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8826 eq9233
  have eq9320 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq9315
  have eq9327 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9320
       have r₂ := eq8825
       grind)
    | exact resolve eq9320 eq8825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9320
  have eq9418 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9327 eq281
    | exact resolve eq281 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9425 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9327 eq181
    | exact resolve eq181 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9477 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9425
    | exact resolve eq9425 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9425
  have eq9479 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq9418
    | exact resolve eq9418 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9418
  have eq9497 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8795 eq9477
    | exact resolve eq9477 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9477
  have eq9576 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq861
       have i₂ := eq9479
       grind)
    | exact superpose eq9479 eq861
    | exact resolve eq861 eq9479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq9479
  have eq9581 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9576
  have eq9602 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9497 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq9497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9647 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq9602
       have r₂ := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq9602 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9602
  have eq9659 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9647
       have r₂ := eq8825
       grind)
    | exact resolve eq9647 eq8825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9647
  have eq9708 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq9581
       grind)
    | exact superpose eq9581 eq180
    | exact resolve eq180 eq9581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9720 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op (M.op x (M.op X1 x)) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 x X1 x x
       have i₂ := eq9581
       grind)
    | exact superpose eq9581 eq179
    | exact resolve eq179 eq9581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq9745 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9720 X0 x
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq9720
    | exact resolve eq9720 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9720
  have eq9753 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9708
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9708
    | exact resolve eq9708 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9708
  have eq9763 : (M.op y (M.op x y)) = (M.op (M.op (M.op x y) x) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9745 x
       have i₂ := eq810 x
       grind)
    | (have i₁ := eq9745 x
       have i₂ := eq810 x
       grind)
    | exact superpose eq810 eq9745
    | (have j0 := eq9745 x
       grind)
    | exact resolve eq9745 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810 eq9745
  have eq9771 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9753 eq9763
    | exact resolve eq9763 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9763
  have eq9779 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9659 eq90
    | exact resolve eq90 eq9659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq9659
  have eq9789 : y = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq9779
    | exact resolve eq9779 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9779
  have eq9797 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9753 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9819 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9797
  have eq9831 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq9819
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq9819 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9819
  have eq9974 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9831 eq35
    | exact resolve eq35 eq9831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9831
  have eq9979 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9974
    | exact resolve eq9974 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9974
  have eq9993 : (k x y) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq9239
       grind)
    | exact superpose eq9239 eq11
    | (have j0 := eq11 x (M.op x y)
       grind)
    | exact resolve eq11 eq9239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9239
  have eq10025 : (M.op x y) = (k x y) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9285 eq9993
    | exact resolve eq9993 eq9285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9993
  have eq10037 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9285 eq10025
    | exact resolve eq10025 eq9285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10025
  have eq10038 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10037
  have eq11465 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9789
       have i₂ := eq10038
       grind)
    | exact superpose eq10038 eq9789
    | exact resolve eq9789 eq10038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9789 eq10038
  have eq11476 : y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq11465
  have eq11484 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11476
       have r₂ := eq8825
       grind)
    | exact resolve eq11476 eq8825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11476
  have eq11496 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq951 y
       have i₂ := eq11484
       grind)
    | exact superpose eq11484 eq951
    | exact resolve eq951 eq11484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11503 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op x (M.op (M.op y X1) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq175 y X1 y x
       have i₂ := eq11484
       grind)
    | exact superpose eq11484 eq175
    | exact resolve eq175 eq11484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq11484
  have eq11544 : ∀ X0 : G, (M.op (M.op x X0) x) = (M.op x (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq11503 X0 x
       have i₂ := eq951 x
       grind)
    | exact superpose eq951 eq11503
    | exact resolve eq11503 eq951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11503
  have eq11547 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11496
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11496
    | exact resolve eq11496 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11496
  have eq11566 : (M.op (M.op x y) x) = (M.op x (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11544 x
       have i₂ := eq197 x
       grind)
    | (have i₁ := eq11544 y
       have i₂ := eq197 x
       grind)
    | exact superpose eq197 eq11544
    | (have j0 := eq11544 y
       grind)
    | exact resolve eq11544 eq197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq11544
  have eq11576 : (M.op x y) = (M.op x (M.op y (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9753 eq11566
    | exact resolve eq11566 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9753 eq11566
  have eq11583 : (M.op x y) = (M.op x (M.op (M.op x y) y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9771 eq11576
    | exact resolve eq11576 eq9771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9771 eq11576
  have eq11594 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11547 eq951
    | exact resolve eq951 eq11547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951 eq11547
  have eq11830 : (M.op x y) ≠ (M.op (M.op x y) y) ∨ (M.op x x) = (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11583 eq12
    | (have j0 := eq12 (M.op (M.op x y) y) x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11583
       grind)
    | exact resolve eq12 eq11583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11583
  have eq11872 : (M.op x x) = (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11830
       have r₂ := eq11594
       grind)
    | exact resolve eq11830 eq11594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11830
  have eq11886 : y = (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9581 eq11872
    | exact resolve eq11872 eq9581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9581 eq11872
  have eq11897 : y = (M.op x y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11594 eq11886
    | exact resolve eq11886 eq11594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11886
  have eq11898 : y = (M.op x y) ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11897
  have eq11903 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11594 eq11898
    | exact resolve eq11898 eq11594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11594 eq11898
  have eq11912 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11903 eq39
    | exact resolve eq39 eq11903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11903
  have eq11916 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq11912
    | exact resolve eq11912 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11912
  have eq11923 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11916 eq902
    | (have j0 := eq902 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq902 (σ x) (σ (M.op x y))
       have r₂ := eq11916
       grind)
    | exact resolve eq902 eq11916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11916
  have eq11924 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11923
  have eq11925 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9327 eq11924
    | exact resolve eq11924 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11924
  have eq11930 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11925
       have r₂ := eq8821
       grind)
    | exact resolve eq11925 eq8821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11925
  have eq11934 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11930 eq203
    | exact resolve eq203 eq11930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11966 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8795 eq11934
    | exact resolve eq11934 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11934
  have eq11976 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9497 eq11966
    | exact resolve eq11966 eq9497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11966
  have eq11995 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11976 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq11976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12030 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11995
       have r₂ := eq8825
       grind)
    | exact resolve eq11995 eq8825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8825 eq11995
  have eq12043 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9979 eq12030
    | exact resolve eq12030 eq9979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9979 eq12030
  have eq12055 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12043
       have r₂ := eq8821
       grind)
    | exact resolve eq12043 eq8821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12043
  have eq12067 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12055 eq16
    | exact resolve eq16 eq12055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12076 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12055 eq182
    | exact resolve eq182 eq12055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq12055
  have eq12097 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11976 eq12076
    | exact resolve eq12076 eq11976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11976 eq12076
  have eq12106 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11930 eq12067
    | exact resolve eq12067 eq11930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11930 eq12067
  have eq12118 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12097 eq12106
    | exact resolve eq12106 eq12097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12097 eq12106
  have eq12126 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq12118
       have r₂ := eq8821
       grind)
    | exact resolve eq12118 eq8821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8821 eq12118
  have eq12134 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12126 eq27
    | exact resolve eq27 eq12126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12136 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12126 eq849
    | exact resolve eq849 eq12126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17479 : (k (σ x) (M.op (σ x) (σ y))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4001 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq4001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17480 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4001 eq12
    | (have j0 := eq12 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq4001
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4001
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4001
       grind)
    | exact resolve eq12 eq4001
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4001
  have eq17533 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8526 eq17480
    | exact resolve eq17480 eq8526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17480
  have eq17534 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17533
  have eq17535 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8526 eq17479
    | exact resolve eq17479 eq8526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17479
  have eq17549 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8526 eq17534
    | exact resolve eq17534 eq8526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17534
  have eq17550 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8526 eq17535
    | exact resolve eq17535 eq8526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8526 eq17535
  have eq17551 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17550
  have eq17564 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq904 (σ x)
       grind)
    | (have r₁ := eq17549
       have r₂ := eq904 (σ x)
       grind)
    | exact resolve eq17549 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17549
  have eq17565 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2877 eq17551
    | exact resolve eq17551 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2877 eq17551
  have eq17578 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12126 eq17564
    | exact resolve eq17564 eq12126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17564
  have eq17579 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9497 eq17565
    | exact resolve eq17565 eq9497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9497 eq17565
  have eq17590 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq17579
       have r₂ := eq17578
       grind)
    | exact resolve eq17579 eq17578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17578 eq17579
  have eq17657 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17590 eq181
    | exact resolve eq181 eq17590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17590
  have eq17719 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq17657
    | exact resolve eq17657 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17657
  have eq17741 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12126 eq17719
    | exact resolve eq17719 eq12126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12126 eq17719
  have eq17742 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17741
  have eq17762 : x = (k (τ (σ x)) x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17742 eq281
    | exact resolve eq281 eq17742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17742
  have eq17828 : x = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq29 eq17762
    | exact resolve eq17762 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17762
  have eq17842 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq9242 x
       grind)
    | (have r₁ := eq17828
       have r₂ := eq9242 x
       grind)
    | (have r₁ := eq17828
       have r₂ := eq9242 (M.op x y)
       grind)
    | exact resolve eq17828 eq9242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9242 eq17828
  have eq17869 : x = y ∨ x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9264
       have i₂ := eq17842
       grind)
    | exact superpose eq17842 eq9264
    | exact resolve eq9264 eq17842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9264
  have eq17878 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq902 x x
       have i₂ := eq17842
       grind)
    | exact superpose eq17842 eq902
    | (have j0 := eq902 x x
       grind)
    | (have r₁ := eq902 x x
       have r₂ := eq17842
       grind)
    | exact resolve eq902 eq17842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17842
  have eq17879 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17878
  have eq17880 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq17879
  have eq17885 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq17869
  have eq17911 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq17885 eq31
    | exact resolve eq31 eq17885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17885
  have eq18095 : x = y ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq17911
    | exact resolve eq17911 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17911
  have eq18096 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18095
  have eq18099 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq18096
       grind)
    | exact superpose eq18096 eq18
    | exact resolve eq18 eq18096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18100 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq18096
       grind)
    | exact superpose eq18096 eq24
    | exact resolve eq24 eq18096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18108 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq847
       have i₂ := eq18096
       grind)
    | exact superpose eq18096 eq847
    | (have r₁ := eq847
       have r₂ := eq18096
       grind)
    | exact resolve eq847 eq18096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq18113 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq18108
  have eq18116 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq18100
    | exact resolve eq18100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18100
  have eq18271 : (M.op (M.op x y) x) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq17880
       grind)
    | exact superpose eq17880 eq180
    | exact resolve eq180 eq17880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17880
  have eq18317 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9227 eq18271
    | exact resolve eq18271 eq9227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9227 eq18271
  have eq18335 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9285 eq18317
    | exact resolve eq18317 eq9285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18317
  have eq18336 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18335
  have eq18439 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18336 eq12136
    | (have r₁ := eq12136
       have r₂ := eq18336
       grind)
    | exact resolve eq12136 eq18336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12136
  have eq18450 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18439
  have eq18451 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18450
  have eq18518 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq904 (σ x)
       grind)
    | (have r₁ := eq18451
       have r₂ := eq904 (σ x)
       grind)
    | exact resolve eq18451 eq904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq904 eq18451
  have eq18556 : x = (k (τ (σ x)) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18518 eq281
    | exact resolve eq281 eq18518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18619 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq18556
    | exact resolve eq18556 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18556
  have eq18736 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq902 x x
       have i₂ := eq18619
       grind)
    | exact superpose eq18619 eq902
    | (have j0 := eq902 x x
       grind)
    | (have r₁ := eq902 x x
       have r₂ := eq18619
       grind)
    | exact resolve eq902 eq18619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18619
  have eq18737 : x ≠ x ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18736
  have eq18738 : x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18737
  have eq18776 : (M.op (M.op x y) x) = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq18738
       grind)
    | exact superpose eq18738 eq180
    | exact resolve eq180 eq18738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18822 : x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18738 eq18776
    | exact resolve eq18776 eq18738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18776
  have eq18857 : x ≠ x ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18822 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq18822
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq18822
       grind)
    | exact resolve eq12 eq18822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18858 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18822 eq16
    | exact resolve eq16 eq18822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18877 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18857
  have eq21883 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18113 eq39
    | exact resolve eq39 eq18113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21889 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq21883
    | exact resolve eq21883 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21883
  have eq21891 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18116 eq21889
    | exact resolve eq21889 eq18116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21889
  have eq21905 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21891 eq863
    | exact resolve eq863 eq21891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21922 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq21905
  have eq28230 : x = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21922 eq281
    | exact resolve eq281 eq21922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28252 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq21922 eq174
    | exact resolve eq174 eq21922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21922
  have eq28338 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1776 eq28252
    | exact resolve eq28252 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28252
  have eq28339 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq28338
  have eq28341 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq28230
    | exact resolve eq28230 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28230
  have eq28366 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1763 eq28341
    | exact resolve eq28341 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28341
  have eq28367 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq28366
  have eq28403 : (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28339 eq21891
    | exact resolve eq21891 eq28339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21891 eq28339
  have eq28408 : (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28403
  have eq28429 : (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18336 eq28408
    | exact resolve eq28408 eq18336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28408
  have eq28430 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28429
  have eq28464 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq28430
       grind)
    | exact superpose eq28430 eq180
    | exact resolve eq180 eq28430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28465 : x = (k (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq174 x
       have i₂ := eq28430
       grind)
    | exact superpose eq28430 eq174
    | exact resolve eq174 eq28430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28467 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq28430
       grind)
    | exact superpose eq28430 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq28430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28496 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28467
  have eq28895 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188
       have i₂ := eq28367
       grind)
    | exact superpose eq28367 eq188
    | exact resolve eq188 eq28367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq28910 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq28367
       grind)
    | exact superpose eq28367 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq28367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28367
  have eq28939 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by grind
  clear eq28910
  have eq28978 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq28895
    | exact resolve eq28895 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28895
  have eq29127 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18116 eq28978
    | exact resolve eq28978 eq18116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28978
  have eq29163 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k y x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq29127
  have eq29174 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1776 eq29163
    | exact resolve eq29163 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29163
  have eq29179 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1776 eq29174
    | exact resolve eq29174 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29174
  have eq29180 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq29179
  have eq29181 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28465 eq29180
    | exact resolve eq29180 eq28465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28465 eq29180
  have eq29195 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28464 eq18099
    | exact resolve eq18099 eq28464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28464
  have eq29257 : (M.op x y) = (M.op (M.op x y) x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29195
  have eq29291 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9285 eq29257
    | exact resolve eq29257 eq9285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9285 eq29257
  have eq29292 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29291
  have eq29313 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29292 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq29292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29292
  have eq29342 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq29313
  have eq29361 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq29342
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq29342 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29342
  have eq29435 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29361 eq35
    | exact resolve eq35 eq29361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29361
  have eq29442 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq29435
    | exact resolve eq29435 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29435
  have eq29651 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29181 eq141
    | exact resolve eq141 eq29181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29657 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29181 eq902
    | (have j0 := eq902 (σ x) (σ x)
       grind)
    | (have r₁ := eq902 (σ x) (σ x)
       have r₂ := eq29181
       grind)
    | exact resolve eq902 eq29181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29181
  have eq29658 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq29657
  have eq29659 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq29658
  have eq29704 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq29651
    | exact resolve eq29651 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29651
  have eq29724 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29659 eq181
    | exact resolve eq181 eq29659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29796 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29659 eq29724
    | exact resolve eq29724 eq29659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29659 eq29724
  have eq29836 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29704 eq37
    | exact resolve eq37 eq29704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq29865 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29836
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29836
    | exact resolve eq29836 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29836
  have eq31676 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18116 eq29865
    | exact resolve eq29865 eq18116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29865
  have eq31712 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq31676
  have eq31719 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1776 eq31712
    | exact resolve eq31712 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31712
  have eq31720 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by grind
  clear eq31719
  have eq31990 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31720 eq107
    | exact resolve eq107 eq31720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq31720
  have eq32014 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq31990
    | exact resolve eq31990 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31990
  have eq32020 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28939 eq32014
    | exact resolve eq32014 eq28939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28939 eq32014
  have eq32021 : x = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32020
  have eq32026 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32021
       have i₂ := eq18096
       grind)
    | exact superpose eq18096 eq32021
    | exact resolve eq32021 eq18096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32034 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq32021
       grind)
    | exact superpose eq32021 eq36
    | exact resolve eq36 eq32021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32045 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq32026
  have eq32049 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32034
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32034
    | exact resolve eq32034 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32034
  have eq32068 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32049 eq863
    | exact resolve eq863 eq32049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32079 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32049 eq902
    | (have j0 := eq902 (σ x) (σ y)
       grind)
    | exact resolve eq902 eq32049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32086 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32068
  have eq32096 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq32079
    | exact resolve eq32079 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32079
  have eq32097 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq32096
  have eq32124 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32045 eq18113
    | exact resolve eq18113 eq32045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18113 eq32045
  have eq32139 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32124
  have eq32179 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq32086
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq32086
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq32086 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32193 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32086 eq203
    | exact resolve eq203 eq32086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32194 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32086 eq181
    | exact resolve eq181 eq32086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32205 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32086 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq32086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32218 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32086 eq805
    | exact resolve eq805 eq32086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32235 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32205
  have eq32256 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq32179
  have eq32281 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq32218
    | (have j0 := eq32218 X0
       grind)
    | exact resolve eq32218 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32218
  have eq32293 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq32194
    | exact resolve eq32194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32194
  have eq32308 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq181 eq32281
    | exact resolve eq32281 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32281
  have eq32325 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32293 eq32308
    | exact resolve eq32308 eq32293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32308
  have eq32359 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq32139
       grind)
    | exact superpose eq32139 eq180
    | exact resolve eq180 eq32139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32362 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq32139
       grind)
    | exact superpose eq32139 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq32139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32139
  have eq32393 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32362
  have eq32435 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18099 eq32359
    | exact resolve eq32359 eq18099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18099 eq32359
  have eq32454 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1825 eq32435
    | exact resolve eq32435 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32435
  have eq32455 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32454
  have eq32484 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32455 eq180
    | exact resolve eq180 eq32455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32485 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32455 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq32455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32516 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32485
  have eq32536 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq32516
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq32516 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32516
  have eq32578 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32484 eq12
    | (have j0 := eq12 (M.op x y) x
       grind)
    | (have r₁ := eq12 (M.op x y) x
       have r₂ := eq32484
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq32484
       grind)
    | exact resolve eq12 eq32484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32484
  have eq32607 : (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32578
  have eq32638 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32536 eq35
    | exact resolve eq35 eq32536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32536
  have eq32645 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq32638
    | exact resolve eq32638 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32638
  have eq32649 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq18116 eq32645
    | exact resolve eq32645 eq18116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32645
  have eq32659 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq32649
  have eq32688 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32293 eq29796
    | exact resolve eq29796 eq32293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29796
  have eq32738 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32688
  have eq32800 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32325 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq32325
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq32325
       grind)
    | exact resolve eq12 eq32325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32325
  have eq32829 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32800
  have eq32839 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32086 eq32829
    | exact resolve eq32829 eq32086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32829
  have eq32840 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq32839
  have eq32873 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq32393
       grind)
    | exact superpose eq32393 eq39
    | exact resolve eq39 eq32393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32874 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1053 x
       have i₂ := eq32393
       grind)
    | exact superpose eq32393 eq1053
    | (have j0 := eq1053 x
       grind)
    | exact resolve eq1053 eq32393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053 eq32393
  have eq32908 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq32874
    | exact resolve eq32874 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32874
  have eq32909 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32873
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32873
    | exact resolve eq32873 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32873
  have eq32911 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32908
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32908
    | exact resolve eq32908 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32908
  have eq32912 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq32909
    | exact resolve eq32909 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32909
  have eq32914 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq32911
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32911
    | exact resolve eq32911 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32911
  have eq32915 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18116 eq32912
    | exact resolve eq32912 eq18116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32912
  have eq32917 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18518 eq32914
    | exact resolve eq32914 eq18518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32914
  have eq32918 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq32917
  have eq33014 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq32915 eq869
    | (have j0 := eq869 (σ x) (σ x) x
       grind)
    | exact resolve eq869 eq32915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32915
  have eq33017 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq33014 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33014
  have eq33044 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq181 eq33017
    | exact resolve eq33017 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33017
  have eq33054 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18518 eq33044
    | exact resolve eq33044 eq18518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18518 eq33044
  have eq33055 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq33054
  have eq34312 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32193 eq32293
    | exact resolve eq32293 eq32193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32193 eq32293
  have eq34365 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq34312
  have eq34459 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34365 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq34365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34491 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq34459
  have eq34608 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32607 eq32738
    | exact resolve eq32738 eq32607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32738
  have eq34616 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq34608
  have eq34659 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq34616
       grind)
    | exact superpose eq34616 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq34616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34616
  have eq34690 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34659
  have eq34793 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq34690
       grind)
    | exact superpose eq34690 eq39
    | exact resolve eq39 eq34690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34829 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34793
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq34793
    | exact resolve eq34793 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34793
  have eq34832 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq34829
    | exact resolve eq34829 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34829
  have eq34893 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq34832 eq869
    | (have j0 := eq869 (σ x) (σ x) x
       grind)
    | exact resolve eq869 eq34832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34896 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq34893 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34893
  have eq34947 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq181 eq34896
    | exact resolve eq34896 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34896
  have eq34954 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33055 eq34947
    | exact resolve eq34947 eq33055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33055 eq34947
  have eq34957 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32086 eq34954
    | exact resolve eq34954 eq32086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32086 eq34954
  have eq34958 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34365 eq34957
    | exact resolve eq34957 eq34365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34957
  have eq35384 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32235 eq34832
    | exact resolve eq34832 eq32235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32235
  have eq35395 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq35384
  have eq35449 : (M.op (σ x) (σ y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq34958
       have i₂ := eq11 sF2 sF1
       grind)
    | exact superpose eq11 eq34958
    | (have j1 := eq11 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq34958 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34958
  have eq35548 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq29442 eq35449
    | exact resolve eq35449 eq29442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29442 eq35449
  have eq35577 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq35548
       have r₂ := eq27
       grind)
    | exact resolve eq35548 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35548
  have eq35596 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq35395 eq35577
    | exact resolve eq35577 eq35395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35577
  have eq35606 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq35395 eq35596
    | exact resolve eq35596 eq35395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35395 eq35596
  have eq35608 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq34365 eq35606
    | exact resolve eq35606 eq34365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34365 eq35606
  have eq35609 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq35608
  have eq35617 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35609 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq35609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35609
  have eq35648 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq35617
  have eq43973 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq32256 eq34832
    | exact resolve eq34832 eq32256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32256 eq34832
  have eq43989 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq43973
  have eq44046 : x = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq43989 eq281
    | exact resolve eq281 eq43989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43989
  have eq44153 : x = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq44046
    | exact resolve eq44046 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44046
  have eq44168 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq34690 eq44153
    | exact resolve eq44153 eq34690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44153
  have eq44169 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq44168
  have eq44183 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq44169 eq849
    | (have r₁ := eq849
       have r₂ := eq44169
       grind)
    | exact resolve eq849 eq44169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44188 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq44183
  have eq45195 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq34491 eq32659
    | exact resolve eq32659 eq34491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32659 eq34491
  have eq45202 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq45195
  have eq45223 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq8795 eq45202
    | exact resolve eq45202 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45202
  have eq45224 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq45223
  have eq45232 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq45224
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq45224
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq45224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45224
  have eq45275 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq45232
  have eq45314 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35648 eq45275
    | exact resolve eq45275 eq35648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35648 eq45275
  have eq49086 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq45314 eq115
    | exact resolve eq115 eq45314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq45314
  have eq49109 : x = (k y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq29 eq49086
    | exact resolve eq49086 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49086
  have eq49116 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8795 eq49109
    | exact resolve eq49109 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49109
  have eq49130 : x = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq49116 eq281
    | exact resolve eq281 eq49116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49116
  have eq49241 : x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq49130
    | exact resolve eq49130 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49130
  have eq49257 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq34690 eq49241
    | exact resolve eq49241 eq34690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34690 eq49241
  have eq49258 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq49257
  have eq49487 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49258 eq41
    | exact resolve eq41 eq49258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq49508 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq49487
    | exact resolve eq49487 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49487
  have eq49511 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq49508
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq49508
    | exact resolve eq49508 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49508
  have eq49514 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44169 eq49511
    | exact resolve eq49511 eq44169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49511
  have eq50042 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq44188 eq141
    | exact resolve eq141 eq44188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44188
  have eq50072 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq31 eq50042
    | exact resolve eq50042 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50042
  have eq50078 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq9327 eq50072
    | exact resolve eq50072 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50072
  have eq50096 : x = (k (τ (σ y)) x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq50078 eq281
    | exact resolve eq281 eq50078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50078
  have eq50231 : x = (k y x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq31 eq50096
    | exact resolve eq50096 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50096
  have eq50275 : x = (k y x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq32021 eq50231
    | exact resolve eq50231 eq32021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50231
  have eq50300 : (M.op x y) = (k (M.op x y) x) ∨ x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq18116 eq50275
    | exact resolve eq50275 eq18116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18116 eq50275
  have eq50722 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ x = (M.op x y) ∨ x = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq50300 eq29704
    | exact resolve eq29704 eq50300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29704 eq50300
  have eq50734 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq50722
  have eq50753 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28496 eq50734
    | exact resolve eq50734 eq28496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28496 eq50734
  have eq50754 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq50753
  have eq50769 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq50754 eq849
    | (have r₁ := eq849
       have r₂ := eq50754
       grind)
    | exact resolve eq849 eq50754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50773 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq50769
  have eq53866 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32049 eq50773
    | exact resolve eq50773 eq32049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32049 eq50773
  have eq53903 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq53866
  have eq53920 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq53903
       have r₂ := eq32097
       grind)
    | exact resolve eq53903 eq32097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32097 eq53903
  have eq53930 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50754 eq53920
    | exact resolve eq53920 eq50754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50754 eq53920
  have eq53948 : x = (k (τ (σ x)) x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53930 eq281
    | exact resolve eq281 eq53930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53930
  have eq54068 : x = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq29 eq53948
    | exact resolve eq53948 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53948
  have eq54266 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq902 x x
       have i₂ := eq54068
       grind)
    | exact superpose eq54068 eq902
    | (have j0 := eq902 x x
       grind)
    | (have r₁ := eq902 x x
       have r₂ := eq54068
       grind)
    | exact resolve eq902 eq54068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54068
  have eq54267 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54266
  have eq54268 : x = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54267
  have eq54335 : (M.op (M.op x y) x) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq54268
       grind)
    | exact superpose eq54268 eq180
    | exact resolve eq180 eq54268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54418 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32455 eq54335
    | exact resolve eq54335 eq32455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54335
  have eq54438 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28430 eq54418
    | exact resolve eq54418 eq28430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28430 eq54418
  have eq54476 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54268
       have i₂ := eq54438
       grind)
    | exact superpose eq54438 eq54268
    | exact resolve eq54268 eq54438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54268
  have eq54484 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq54438
       grind)
    | exact superpose eq54438 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq54438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54438
  have eq54526 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq54484
  have eq54530 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq54476
  have eq54764 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq54526
       grind)
    | exact superpose eq54526 eq39
    | exact resolve eq39 eq54526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54526
  have eq54802 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq54764
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq54764
    | exact resolve eq54764 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54764
  have eq54813 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq54802
    | exact resolve eq54802 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54802
  have eq54817 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54530 eq54813
    | exact resolve eq54813 eq54530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54530 eq54813
  have eq62839 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq877 x
       have i₂ := eq4481
       grind)
    | exact superpose eq4481 eq877
    | (have j0 := eq877 x
       grind)
    | exact resolve eq877 eq4481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq877 eq4481
  have eq62961 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq62839
  have eq63018 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq62961
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq62961
    | exact resolve eq62961 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62961
  have eq63048 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1825 eq63018
    | exact resolve eq63018 eq1825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1825 eq63018
  have eq63064 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8795 eq63048
    | exact resolve eq63048 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63048
  have eq63065 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq63064
  have eq63123 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54817 eq878
    | (have j0 := eq878 (σ x)
       grind)
    | exact resolve eq878 eq54817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878 eq54817
  have eq63217 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq63123
  have eq63306 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq63217
       have r₂ := eq32918
       grind)
    | exact resolve eq63217 eq32918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32918 eq63217
  have eq63352 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq63306
    | exact resolve eq63306 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63306
  have eq63419 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63065 eq174
    | exact resolve eq174 eq63065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63510 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63419 eq5857
    | exact resolve eq5857 eq63419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5857 eq63419
  have eq63531 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq63510
  have eq63541 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8795 eq63531
    | exact resolve eq63531 eq8795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8795 eq63531
  have eq63545 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63065 eq63541
    | exact resolve eq63541 eq63065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63065 eq63541
  have eq63546 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq63545
  have eq63553 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63546 eq27
    | exact resolve eq27 eq63546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63555 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63546 eq849
    | (have r₁ := eq849
       have r₂ := eq63546
       grind)
    | exact resolve eq849 eq63546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63560 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq63555
  have eq65083 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63560 eq1420
    | exact resolve eq1420 eq63560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65096 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63560 eq141
    | exact resolve eq141 eq63560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq63560
  have eq65110 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq65083
  have eq65126 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq65096
    | exact resolve eq65096 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65096
  have eq65128 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq65110
       have r₂ := eq63553
       grind)
    | exact resolve eq65110 eq63553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63553 eq65110
  have eq65134 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9327 eq65126
    | exact resolve eq65126 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65126
  have eq65136 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9327 eq65128
    | exact resolve eq65128 eq9327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9327 eq65128
  have eq65190 : (σ x) = (k (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65134 eq174
    | exact resolve eq174 eq65134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65134
  have eq65315 : (σ x) = (k (σ y) (σ x)) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1776 eq65190
    | exact resolve eq65190 eq1776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776 eq65190
  have eq65449 : x = (k (τ (σ y)) x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq65136 eq281
    | exact resolve eq281 eq65136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65136
  have eq65615 : x = (k y x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq65449
    | exact resolve eq65449 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65449
  have eq65655 : x = (k y x) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1763 eq65615
    | exact resolve eq65615 eq1763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1763 eq65615
  have eq65687 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq18336 eq65655
    | exact resolve eq65655 eq18336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65655
  have eq65703 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq13 y (M.op x y)
       grind)
    | (have r₁ := eq65687
       have r₂ := eq13 y (M.op x y)
       grind)
    | exact resolve eq65687 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65687
  have eq66987 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op (σ y) X1) (σ y))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | exact superpose eq2158 eq2367
    | exact resolve eq2367 eq2158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2158 eq2367
  have eq67477 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq971 eq66987
    | exact resolve eq66987 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq66987
  have eq67730 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) = (M.op (M.op (M.op (σ x) X0) (σ x)) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq63546 eq67477
    | exact resolve eq67477 eq63546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67477
  have eq67896 : (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq203 eq67730
    | (have j0 := eq67730 (σ y)
       grind)
    | exact resolve eq67730 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq67730
  have eq67995 : (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq63546 eq67896
    | exact resolve eq67896 eq63546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67896
  have eq68063 : (M.op (σ y) (M.op (σ y) (σ x))) = (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1685 eq67995
    | exact resolve eq67995 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67995
  have eq68104 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq2138 eq68063
    | exact resolve eq68063 eq2138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68063
  have eq68124 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq63546 eq68104
    | exact resolve eq68104 eq63546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63546 eq68104
  have eq68137 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1685 eq68124
    | exact resolve eq68124 eq1685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685 eq68124
  have eq70048 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq68137 eq2138
    | exact resolve eq2138 eq68137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138 eq68137
  have eq70165 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq70048
  have eq70230 : y = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq70165
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq70165
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq70165 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70253 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq70165
       grind)
    | exact superpose eq70165 eq180
    | exact resolve eq180 eq70165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70256 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq70165
       grind)
    | exact superpose eq70165 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq70165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70278 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq805 x x X0
       have i₂ := eq70165
       grind)
    | exact superpose eq70165 eq805
    | exact resolve eq805 eq70165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq70304 : y = (k x x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq70256
  have eq70322 : y = (k x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq70230
  have eq70358 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq70278 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq70278
    | (have j0 := eq70278 X0
       grind)
    | exact resolve eq70278 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70278
  have eq70379 : y = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18096 eq70304
    | exact resolve eq70304 eq18096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18096 eq70304
  have eq70380 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70253
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq70253
    | exact resolve eq70253 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70253
  have eq70386 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq18738 eq70322
    | exact resolve eq70322 eq18738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18738 eq70322
  have eq70409 : (M.op (M.op x y) x) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq70358 x
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq70358
    | exact resolve eq70358 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70358
  have eq70443 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70380 eq70409
    | exact resolve eq70409 eq70380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70409
  have eq70478 : x ≠ (M.op x y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq70380 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq70380
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq70380
       grind)
    | exact resolve eq12 eq70380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70561 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq70478
       have r₂ := eq18877
       grind)
    | exact resolve eq70478 eq18877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18877 eq70478
  have eq72626 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq70561 eq869
    | (have j0 := eq869 x (M.op x y) x
       grind)
    | exact resolve eq869 eq70561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70561
  have eq72630 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq72626 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72626
  have eq72647 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18858 eq72630
    | (have j0 := eq72630 X0
       have j1 := eq18858 X0
       grind)
    | exact resolve eq72630 eq18858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72630
  have eq72659 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq18858 eq72647
    | (have j0 := eq72647 X0
       have j1 := eq18858 X0
       grind)
    | exact resolve eq72647 eq18858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18858 eq72647
  have eq72660 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq72659 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72659
  have eq72665 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq70443 eq72660
    | exact resolve eq72660 eq70443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70443 eq72660
  have eq85689 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq63352 eq181
    | exact resolve eq181 eq63352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq63352
  have eq86796 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq85689 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq12 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq85689
       grind)
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq85689
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq85689
       grind)
    | exact resolve eq12 eq85689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85689
  have eq86852 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq86796
  have eq86873 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32840 eq86852
    | exact resolve eq86852 eq32840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32840 eq86852
  have eq86874 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq86873
  have eq110176 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq72665 eq881
    | exact resolve eq881 eq72665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq110218 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq110176 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110176
  have eq110317 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq72665 eq110218
    | exact resolve eq110218 eq72665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72665 eq110218
  have eq110345 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq110317
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq110317 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110317
  have eq110509 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq110345 eq70379
    | exact resolve eq70379 eq110345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70379
  have eq110510 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq110345 eq70386
    | exact resolve eq70386 eq110345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70386 eq110345
  have eq110526 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq110510
  have eq110527 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq110509
  have eq112807 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq110527 eq849
    | (have r₁ := eq849
       have r₂ := eq110527
       grind)
    | exact resolve eq849 eq110527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110527
  have eq112813 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq112807
  have eq112911 : (M.op (M.op x y) x) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq110526
       grind)
    | exact superpose eq110526 eq180
    | exact resolve eq180 eq110526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110526
  have eq113050 : y = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq70165 eq112911
    | exact resolve eq112911 eq70165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70165 eq112911
  have eq113080 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq70380 eq113050
    | exact resolve eq113050 eq70380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70380 eq113050
  have eq113081 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq113080
  have eq113118 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113081 eq27
    | exact resolve eq27 eq113081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113120 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113081 eq849
    | (have r₁ := eq849
       have r₂ := eq113081
       grind)
    | exact resolve eq849 eq113081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849 eq113081
  have eq113126 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq113120
  have eq113692 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113126 eq1420
    | exact resolve eq1420 eq113126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113704 : (σ x) = (σ y) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113126 eq65315
    | exact resolve eq65315 eq113126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65315 eq113126
  have eq113714 : (σ x) = (σ y) ∨ y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq113704
  have eq113723 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq113692
  have eq113743 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq65703 eq113714
    | exact resolve eq113714 eq65703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65703 eq113714
  have eq113744 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq113743
  have eq113745 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq113723
       have r₂ := eq113118
       grind)
    | exact resolve eq113723 eq113118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113723
  have eq113828 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq113744 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq113744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113744
  have eq113895 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq113828
  have eq114252 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113895 eq97
    | exact resolve eq97 eq113895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113895
  have eq114332 : y = (k x x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq114252
    | exact resolve eq114252 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114252
  have eq114340 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18336 eq114332
    | exact resolve eq114332 eq18336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18336 eq114332
  have eq115290 : x = (k (τ (σ y)) x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq113745 eq281
    | exact resolve eq281 eq113745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281 eq113745
  have eq115507 : x = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq115290
    | exact resolve eq115290 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115290
  have eq115563 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq115507
       have r₂ := eq13 y x
       grind)
    | exact resolve eq115507 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115507
  have eq115673 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq115563
       grind)
    | exact superpose eq115563 eq36
    | exact resolve eq36 eq115563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq115675 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq869 y x X0
       have i₂ := eq115563
       grind)
    | exact superpose eq115563 eq869
    | (have j0 := eq869 y x x
       grind)
    | exact resolve eq869 eq115563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq115563
  have eq115686 : (M.op (M.op x y) x) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq115675 x
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq115675
    | exact resolve eq115675 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115675
  have eq115688 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq115673
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq115673
    | exact resolve eq115673 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115673
  have eq115691 : y = (M.op x y) ∨ (M.op (M.op x y) x) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq115686
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115686
    | exact resolve eq115686 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115686
  have eq115692 : (M.op (M.op x y) x) = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq115691
  have eq115712 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115688 eq1420
    | exact resolve eq1420 eq115688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq115735 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq115712
  have eq115793 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq115735
       grind)
    | exact superpose eq115735 eq180
    | exact resolve eq180 eq115735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115735
  have eq115970 : (M.op x y) = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq115793
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115793
    | exact resolve eq115793 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115793
  have eq116084 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq115970
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq115970
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq115970 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116088 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq115970 eq18822
    | exact resolve eq18822 eq115970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115970
  have eq116185 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq116088
  have eq116234 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq116185
       have r₂ := eq12134
       grind)
    | exact resolve eq116185 eq12134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12134 eq116185
  have eq116236 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have j1 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq116084
       have r₂ := eq13 x (M.op x y)
       grind)
    | exact resolve eq116084 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116084
  have eq116278 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq116234 eq116236
    | exact resolve eq116236 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116236
  have eq116292 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq116234 eq116278
    | exact resolve eq116278 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116278
  have eq116300 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq116292
       have r₂ := eq13 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq116292 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116292
  have eq116303 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq116234
       grind)
    | exact superpose eq116234 eq24
    | exact resolve eq24 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116306 : (σ y) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq187
       have i₂ := eq116234
       grind)
    | exact superpose eq116234 eq187
    | exact resolve eq187 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116314 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq960
       have i₂ := eq116234
       grind)
    | exact superpose eq116234 eq960
    | exact resolve eq960 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq116315 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32021
       have i₂ := eq116234
       grind)
    | exact superpose eq116234 eq32021
    | exact resolve eq32021 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32021
  have eq116316 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq116315
  have eq116320 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq116303
    | exact resolve eq116303 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116303
  have eq120892 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq116300 eq114340
    | exact resolve eq114340 eq116300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116300
  have eq120907 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq120892
  have eq120940 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq120907 eq31
    | exact resolve eq31 eq120907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120907
  have eq121257 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq120940
    | exact resolve eq120940 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120940
  have eq121277 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq116234 eq121257
    | exact resolve eq121257 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121257
  have eq121278 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq121277
  have eq121305 : (M.op x y) = (k (τ (M.op (σ x) (σ x))) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq121278 eq337
    | exact resolve eq337 eq121278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq121424 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq121278 eq113118
    | exact resolve eq113118 eq121278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113118 eq121278
  have eq121430 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq121424
  have eq122475 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116316 eq32607
    | exact resolve eq32607 eq116316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32607 eq116316
  have eq122494 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq122475
  have eq122627 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq122494
       grind)
    | exact superpose eq122494 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq122494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122494
  have eq122698 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq122627
  have eq122913 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq122698
       grind)
    | exact superpose eq122698 eq39
    | exact resolve eq39 eq122698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq122698
  have eq122962 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq122913
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq122913
    | exact resolve eq122913 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122913
  have eq122967 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq122962
    | exact resolve eq122962 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122962
  have eq122971 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq116320 eq122967
    | exact resolve eq122967 eq116320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122967
  have eq123888 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq116314
       have i₂ := eq11 sF0 sF0
       grind)
    | exact superpose eq11 eq116314
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq116314 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116314
  have eq124062 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq123888
  have eq130478 : (k x x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq115692
       grind)
    | exact superpose eq115692 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq115692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115692
  have eq130552 : (k x x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq130478
  have eq130620 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18822 eq130552
    | exact resolve eq130552 eq18822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130552
  have eq130650 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18822 eq130620
    | exact resolve eq130620 eq18822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18822 eq130620
  have eq130663 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq116234 eq130650
    | exact resolve eq130650 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130650
  have eq130670 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11 eq130663
    | (have j1 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq130663 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130663
  have eq130671 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq130670
  have eq134661 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq112813 eq115688
    | exact resolve eq115688 eq112813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112813 eq115688
  have eq134669 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq134661
  have eq134708 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq134669
       have r₂ := eq121430
       grind)
    | exact resolve eq134669 eq121430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134669
  have eq134723 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq116234 eq134708
    | exact resolve eq134708 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134708
  have eq134724 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq134723
  have eq134754 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq134724
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq134724
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq134724 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134724
  have eq134906 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq134754
  have eq135774 : (τ (σ y)) = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq134906 eq97
    | exact resolve eq97 eq134906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134906
  have eq135853 : y = (k x x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31 eq135774
    | exact resolve eq135774 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135774
  have eq135860 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq116234 eq135853
    | exact resolve eq135853 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135853
  have eq135908 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq135860 eq121305
    | exact resolve eq121305 eq135860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121305 eq135860
  have eq136016 : (M.op x y) = (k (τ (σ x)) (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq135908
  have eq136082 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq136016
    | exact resolve eq136016 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136016
  have eq136109 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq116234 eq136082
    | exact resolve eq136082 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136082
  have eq136307 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq136109 eq902
    | (have j0 := eq902 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq902 (M.op x y) (M.op x y)
       have r₂ := eq136109
       grind)
    | exact resolve eq902 eq136109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902 eq136109
  have eq136309 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq136307
  have eq136310 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq136309
  have eq149393 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq49258 eq124062
    | exact resolve eq124062 eq49258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49258 eq124062
  have eq149553 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq149393
  have eq149608 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32455 eq149553
    | exact resolve eq149553 eq32455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32455 eq149553
  have eq149609 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq149608
  have eq149663 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq149609 eq116306
    | exact resolve eq116306 eq149609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116306 eq149609
  have eq149836 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq149663
  have eq149848 : (σ y) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq149836
    | exact resolve eq149836 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149836
  have eq149856 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44169 eq149848
    | exact resolve eq149848 eq44169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44169 eq149848
  have eq149860 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq49514 eq149856
    | exact resolve eq149856 eq49514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49514 eq149856
  have eq149864 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq149860 eq27
    | exact resolve eq27 eq149860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149860
  have eq149880 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq149864
       have r₂ := eq116320
       grind)
    | exact resolve eq149864 eq116320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116320 eq149864
  have eq149929 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq149880 eq86874
    | exact resolve eq86874 eq149880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86874
  have eq149936 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq149929
  have eq149980 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq149936
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq149936 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149936
  have eq150334 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq149980 eq122971
    | exact resolve eq122971 eq149980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122971 eq149980
  have eq150353 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq150334
  have eq150423 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq149880 eq150353
    | exact resolve eq150353 eq149880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149880 eq150353
  have eq150424 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq150423
  have eq150447 : y = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq150424 eq31
    | exact resolve eq31 eq150424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150424
  have eq150802 : x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq150447
    | exact resolve eq150447 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq150447
  have eq150819 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116234 eq150802
    | exact resolve eq150802 eq116234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116234 eq150802
  have eq150820 : x = (M.op x y) := by grind
  clear eq150819
  have eq150823 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq150820
       grind)
    | exact superpose eq150820 eq18
    | exact resolve eq18 eq150820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq150824 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq150820
       grind)
    | exact superpose eq150820 eq22
    | exact resolve eq22 eq150820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq150825 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq150820
       grind)
    | exact superpose eq150820 eq35
    | exact resolve eq35 eq150820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq150827 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq150820
       grind)
    | exact superpose eq150820 eq180
    | exact resolve eq180 eq150820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq150901 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq150824 eq20
    | exact resolve eq20 eq150824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151994 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114340 eq150825
    | exact resolve eq150825 eq114340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114340 eq150825
  have eq152110 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq151994
       have r₂ := eq121430
       grind)
    | exact resolve eq151994 eq121430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121430 eq151994
  have eq152147 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq152110
    | exact resolve eq152110 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152110
  have eq152160 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150901 eq152147
    | exact resolve eq152147 eq150901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152147
  have eq152165 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq152160
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq152160
    | exact resolve eq152160 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152160
  have eq152195 : (τ (σ y)) = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq152165 eq97
    | exact resolve eq97 eq152165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq152165
  have eq152275 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq152195
       have i₂ := eq150820
       grind)
    | exact superpose eq150820 eq152195
    | exact resolve eq152195 eq150820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150820 eq152195
  have eq152282 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq152275
    | exact resolve eq152275 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq152275
  have eq152764 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq130671 eq150827
    | exact resolve eq150827 eq130671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130671 eq150827
  have eq152998 : y = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq136310 eq152764
    | exact resolve eq152764 eq136310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136310 eq152764
  have eq153031 : y = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150823 eq152998
    | exact resolve eq152998 eq150823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152998
  have eq153032 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq153031
  have eq153120 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq153032 eq174
    | exact resolve eq174 eq153032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq153032
  have eq153276 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq153120 eq152282
    | exact resolve eq152282 eq153120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152282 eq153120
  have eq153293 : y = (M.op x y) := by grind
  clear eq153276
  have eq153329 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq153293
       grind)
    | exact superpose eq153293 eq24
    | exact resolve eq24 eq153293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq153332 : (σ y) = (k (σ (M.op (M.op x y) (M.op x y))) (σ y)) := by
    first
    | (have i₁ := eq187
       have i₂ := eq153293
       grind)
    | exact superpose eq153293 eq187
    | exact resolve eq187 eq153293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq153342 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq150823
       have i₂ := eq153293
       grind)
    | exact superpose eq153293 eq150823
    | exact resolve eq150823 eq153293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150823 eq153293
  have eq153345 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq153342 eq153332
    | exact resolve eq153332 eq153342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153332 eq153342
  have eq153348 : (σ x) = (σ y) := by
    first
    | exact superpose eq150824 eq153329
    | exact resolve eq153329 eq150824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150824 eq153329
  have eq153350 : (σ y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq153345
    | exact resolve eq153345 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq153345
  have eq153351 : (σ x) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq153348 eq153350
    | exact resolve eq153350 eq153348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153350
  have eq153352 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq150901 eq153351
    | exact resolve eq153351 eq150901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153351
  have eq153353 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq153348 eq26
    | exact resolve eq26 eq153348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq153374 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq153348 eq863
    | exact resolve eq863 eq153348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq863 eq153348
  have eq153601 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq153352 eq153374
    | exact resolve eq153374 eq153352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153352 eq153374
  have eq153602 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq153601
  have eq153622 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq153353 eq153602
    | exact resolve eq153602 eq153353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153353 eq153602
  have eq153623 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq153622
  have eq153648 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq153623 eq27
    | exact resolve eq27 eq153623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq153623
  have eq153706 : False := by grind
  exact eq153706
