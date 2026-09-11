import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq64 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq768 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq366 x y
       grind)
    | exact superpose eq366 eq16
    | (have j1 := eq366 x y
       grind)
    | exact resolve eq16 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq770 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) (M.op (σ X1) X2))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X1) X2
       have i₂ := eq366 X1 X0
       grind)
    | exact superpose eq366 eq9
    | (have j1 := eq366 X1 X0
       grind)
    | exact resolve eq9 eq366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq792 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq366 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq795 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq791 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq798 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq795 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq795
    | (have j0 := eq795 X0
       grind)
    | exact resolve eq795 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq3197 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (σ (k (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq798 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq798
    | exact resolve eq798 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3241 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  clear eq798
  have eq3243 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq3241 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq3241
    | (have j0 := eq3241 X0
       grind)
    | exact resolve eq3241 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3241
  have eq3247 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k (σ (τ X0)) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3197 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3197
    | (have j0 := eq3197 X0
       grind)
    | exact resolve eq3197 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197
  have eq3250 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3247 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3247
    | (have j0 := eq3247 X0
       grind)
    | exact resolve eq3247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3247
  have eq3251 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3250 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq3250
    | (have j0 := eq3250 X0
       grind)
    | exact resolve eq3250 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3250
  have eq3252 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k (σ (τ X0)) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3251 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3251
    | (have j0 := eq3251 X0
       grind)
    | exact resolve eq3251 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3251
  have eq3253 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3252 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3252
    | (have j0 := eq3252 X0
       grind)
    | exact resolve eq3252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252
  have eq5879 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq363 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq363
    | exact resolve eq363 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq5930 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5879 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5879
    | (have j0 := eq5879 X0 X1
       grind)
    | exact resolve eq5879 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5879
  have eq5998 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (τ (k (σ (M.op X0 X1)) X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29 (k X1 X0) X2
       have i₂ := eq5930 X0 X1
       grind)
    | exact superpose eq5930 eq29
    | (have j1 := eq5930 X0 X1
       grind)
    | exact resolve eq29 eq5930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6015 : ∀ X0 X1 X2 : G, (k (k X1 X0) (τ X2)) = (k (M.op X0 X1) (τ X2)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5998 X0 X1 X2
       have i₂ := eq29 (M.op X0 X1) X2
       grind)
    | exact superpose eq29 eq5998
    | (have j0 := eq5998 X0 X1 X2
       grind)
    | exact resolve eq5998 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5998
  have eq6373 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq768
       have i₂ := eq5930 x y
       grind)
    | exact superpose eq5930 eq768
    | (have j1 := eq5930 (σ x) (σ y)
       grind)
    | (have r₁ := eq768
       have r₂ := eq5930 x y
       grind)
    | exact resolve eq768 eq5930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq6374 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq6373
  have eq7903 : ∀ X0 X1 X2 : G, (k (k X1 X2) X0) = (k (M.op X2 X1) X0) ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6015 X0 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6015
    | (have j0 := eq6015 X2 X1 X2
       grind)
    | exact resolve eq6015 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6015
  have eq8065 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3253 X0
       have i₂ := eq7903 X0 X0 X0
       grind)
    | exact superpose eq7903 eq3253
    | (have j0 := eq3253 X0
       have j1 := eq7903 X0 X0 X0
       grind)
    | exact resolve eq3253 eq7903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3253 eq7903
  have eq8159 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq8065 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8065
  have eq8196 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq8159
  have eq13464 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    grind
  clear eq3243
  have eq13538 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq13464 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq13464
    | (have j0 := eq13464 X0
       grind)
    | exact resolve eq13464 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13464
  have eq13539 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq13538 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13538
  have eq13603 : ∀ X0 : G, (σ (k (σ (k X0 X0)) (σ X0))) = (M.op (σ (σ X0)) (σ (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq13539 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq13539
    | exact resolve eq13539 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13621 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq13539 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq13539
    | exact resolve eq13539 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13539
  have eq13684 : ∀ X0 : G, (σ (k (k (τ X0) (τ X0)) (τ X0))) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13621 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13621
    | exact resolve eq13621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13621
  have eq13695 : ∀ X0 : G, (σ (σ (k (k X0 X0) X0))) = (M.op (σ (σ X0)) (σ (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq13603 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq13603
    | exact resolve eq13603 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13603
  have eq13715 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (σ (k (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq13684 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq13684
    | exact resolve eq13684 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13684
  have eq13739 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k (σ (τ X0)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13715 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq13715
    | exact resolve eq13715 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13715
  have eq13757 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13739 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq13739
    | exact resolve eq13739 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13739
  have eq13806 : ∀ X0 : G, (k (τ (k X0 X0)) (τ X0)) = (M.op (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13757 (τ X0)
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq13757
    | exact resolve eq13757 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13938 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (τ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq13806 X0
       have i₂ := eq32 X0 (k X0 X0)
       grind)
    | exact superpose eq32 eq13806
    | exact resolve eq13806 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13806
  have eq13994 : ∀ X0 : G, (M.op (τ X0) (τ (k X0 X0))) = (τ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13938 X0
       have i₂ := eq13757 X0
       grind)
    | exact superpose eq13757 eq13938
    | exact resolve eq13938 eq13757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13938
  have eq15724 : ∀ X0 : G, (σ (σ (k (σ (k X0 X0)) (σ X0)))) = (M.op (σ (σ (σ X0))) (σ (σ (σ (k X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq13695 (σ x)
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq13695
    | exact resolve eq13695 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13695
  have eq15863 : ∀ X0 : G, (σ (σ (σ (k (k X0 X0) X0)))) = (M.op (σ (σ (σ X0))) (σ (σ (σ (k X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq15724 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq15724
    | exact resolve eq15724 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15724
  have eq15928 : ∀ X0 : G, (σ (σ (σ (M.op X0 (k X0 X0))))) = (M.op (σ (σ (σ X0))) (σ (σ (σ (k X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq15863 X0
       have i₂ := eq13757 X0
       grind)
    | exact superpose eq13757 eq15863
    | exact resolve eq15863 eq13757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13757 eq15863
  have eq21710 : ∀ X0 : G, (σ (σ (σ (M.op (τ X0) (k (τ X0) (τ X0)))))) = (M.op (σ (σ (σ (τ X0)))) (σ (σ (k X0 (σ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq15928 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq15928
    | exact resolve eq15928 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15928
  have eq21786 : ∀ X0 : G, (M.op (σ (σ X0)) (σ (σ (k X0 X0)))) = (σ (σ (σ (M.op (τ X0) (k (τ X0) (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq21710 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq21710
    | exact resolve eq21710 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21710
  have eq21827 : ∀ X0 : G, (M.op (σ (σ X0)) (σ (σ (k X0 X0)))) = (σ (σ (σ (M.op (τ X0) (τ (k X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq21786 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq21786
    | exact resolve eq21786 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21786
  have eq21858 : ∀ X0 : G, (M.op (σ (σ X0)) (σ (σ (k X0 X0)))) = (σ (σ (σ (τ (M.op X0 (k X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq21827 X0
       have i₂ := eq13994 X0
       grind)
    | exact superpose eq13994 eq21827
    | exact resolve eq21827 eq13994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21827
  have eq21885 : ∀ X0 : G, (σ (σ (M.op X0 (k X0 X0)))) = (M.op (σ (σ X0)) (σ (σ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq21858 X0
       have i₂ := eq11 (M.op X0 (k X0 X0))
       grind)
    | exact superpose eq11 eq21858
    | exact resolve eq21858 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21858
  have eq21969 : ∀ X0 : G, (M.op (σ (σ (τ X0))) (σ (k X0 (σ (τ X0))))) = (σ (σ (M.op (τ X0) (k (τ X0) (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq21885 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq21885
    | exact resolve eq21885 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq21885
  have eq22049 : ∀ X0 : G, (σ (σ (M.op (τ X0) (τ (k X0 X0))))) = (M.op (σ (σ (τ X0))) (σ (k X0 (σ (τ X0))))) := by
    intro X0
    first
    | (have i₁ := eq21969 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq21969
    | exact resolve eq21969 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq21969
  have eq22101 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (σ (M.op (τ X0) (τ (k X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq22049 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22049
    | exact resolve eq22049 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22049
  have eq22132 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (σ (τ (M.op X0 (k X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq22101 X0
       have i₂ := eq13994 X0
       grind)
    | exact superpose eq13994 eq22101
    | exact resolve eq22101 eq13994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13994 eq22101
  have eq22154 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22132 X0
       have i₂ := eq11 (M.op X0 (k X0 X0))
       grind)
    | exact superpose eq11 eq22132
    | exact resolve eq22132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22132
  have eq46511 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq770 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770
  have eq46512 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) (M.op (σ X0) X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq46511 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46511
  have eq46891 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq46512 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq46512
    | exact resolve eq46512 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46512
  have eq47075 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq46891 X0 X1
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq46891
    | (have j0 := eq46891 X0 X1
       grind)
    | exact resolve eq46891 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46891
  have eq47118 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq47075 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq47075
    | (have j0 := eq47075 X0 X1
       grind)
    | exact resolve eq47075 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47075
  have eq47329 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 (k X0 X0) X0 (M.op X0 x)
       have i₂ := eq47118 X0 x
       grind)
    | exact superpose eq47118 eq9
    | (have j1 := eq47118 X0 x
       grind)
    | exact resolve eq9 eq47118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47118
  have eq47481 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47329 X0
       have i₂ := eq8196 X0
       grind)
    | exact superpose eq8196 eq47329
    | (have j0 := eq47329 X0
       have j1 := eq8196 X0
       grind)
    | exact resolve eq47329 eq8196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8196 eq47329
  have eq47596 : ∀ X0 : G, (k X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq47481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47481
  have eq47633 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47596 X0
       have i₂ := eq64 X0 X0
       grind)
    | exact superpose eq64 eq47596
    | (have j0 := eq47596 X0
       grind)
    | exact resolve eq47596 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq47596
  have eq47856 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq47633 (σ X0)
       grind)
    | exact superpose eq47633 eq15
    | (have j1 := eq47633 (σ X0)
       grind)
    | exact resolve eq15 eq47633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47633
  have eq48196 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq47856
  have eq48266 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48196 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq48196
    | (have j0 := eq48196 X0
       grind)
    | exact resolve eq48196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48196
  have eq48267 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq48266 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48266
  have eq48340 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq48267 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48267
    | exact resolve eq48267 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48672 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq48340 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq48340
    | exact resolve eq48340 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq48340
  have eq48756 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq48672 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48672
    | exact resolve eq48672 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48672
  have eq49029 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22154 X0
       have i₂ := eq48756 X0
       grind)
    | exact superpose eq48756 eq22154
    | exact resolve eq22154 eq48756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22154
  have eq605639 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq6374
       grind)
    | exact superpose eq6374 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6374
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq6374
       grind)
    | exact resolve eq13 eq6374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6374
  have eq605720 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq605639
  have eq605721 : y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq605720
  have eq605798 : (σ y) = (σ (k x x)) ∨ y = (M.op x x) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq605721
       have i₂ := eq48267 x
       grind)
    | exact superpose eq48267 eq605721
    | exact resolve eq605721 eq48267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605721
  have eq605874 : y = (k y x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq605798
       have i₂ := eq48756 x
       grind)
    | exact superpose eq48756 eq605798
    | exact resolve eq605798 eq48756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605798
  have eq605899 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq792 x y
       have i₂ := eq605874
       grind)
    | exact superpose eq605874 eq792
    | (have j0 := eq792 x y
       grind)
    | exact resolve eq792 eq605874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792 eq605874
  have eq605989 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq605899
  have eq605990 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq605989
  have eq605999 : (σ y) = (σ (k x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq605990
       have i₂ := eq48267 x
       grind)
    | exact superpose eq48267 eq605990
    | exact resolve eq605990 eq48267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605990
  have eq606006 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq605999
       have i₂ := eq48756 x
       grind)
    | exact superpose eq48756 eq605999
    | exact resolve eq605999 eq48756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605999
  have eq606007 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq606006
  have eq606016 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq606007
       grind)
    | exact superpose eq606007 eq16
    | exact resolve eq16 eq606007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606085 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq606007
       grind)
    | exact superpose eq606007 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq606007
       grind)
    | exact resolve eq13 eq606007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606007
  have eq606166 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq606085
  have eq606197 : (σ y) = (σ (k x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq606166
       have i₂ := eq48267 x
       grind)
    | exact superpose eq48267 eq606166
    | exact resolve eq606166 eq48267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48267 eq606166
  have eq606261 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq606197
       have i₂ := eq48756 x
       grind)
    | exact superpose eq48756 eq606197
    | exact resolve eq606197 eq48756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48756 eq606197
  have eq606262 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq606261
  have eq606285 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq606262
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq606262
    | exact resolve eq606262 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606262
  have eq606314 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5930 x y
       have i₂ := eq606285
       grind)
    | exact superpose eq606285 eq5930
    | (have j0 := eq5930 x y
       grind)
    | exact resolve eq5930 eq606285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5930 eq606285
  have eq606689 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq606314
  have eq606912 : y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq606689
       have r₂ := eq606016
       grind)
    | exact resolve eq606689 eq606016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606689
  have eq607222 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq606016
       have i₂ := eq606912
       grind)
    | exact superpose eq606912 eq606016
    | exact resolve eq606016 eq606912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606016 eq606912
  have eq607308 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq607222
  have eq607309 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq607308
  have eq607507 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq49029 x
       have i₂ := eq607309
       grind)
    | exact superpose eq607309 eq49029
    | exact resolve eq49029 eq607309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607309
  have eq607802 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq607507
       have r₂ := eq16
       grind)
    | exact resolve eq607507 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607507
  have eq608047 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq607802
       grind)
    | exact superpose eq607802 eq10
    | exact resolve eq10 eq607802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607802
  have eq608654 : y = (M.op x x) := by
    first
    | (have i₁ := eq608047
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq608047
    | exact resolve eq608047 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608047
  have eq609213 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49029 x
       have i₂ := eq608654
       grind)
    | exact superpose eq608654 eq49029
    | exact resolve eq49029 eq608654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49029 eq608654
  have eq609509 : False := by grind
  exact eq609509

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation1483 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq1163 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1250 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1163 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1251 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1250 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250
  have eq1396 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1251 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1399 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1396 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1396 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1396 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq1396 X0 X1
       have r₂ := eq14 (M.op X1 X0) (M.op X0 X0)
       grind)
    | exact resolve eq1396 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1451 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq1399 X1 (τ X0)
       grind)
    | exact superpose eq1399 eq19
    | (have j1 := eq1399 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1454 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1399 (σ X1) (σ X0)
       grind)
    | exact superpose eq1399 eq15
    | (have j1 := eq1399 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq1399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1399
  have eq1553 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1451 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1451
    | exact resolve eq1451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1451
  have eq1607 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1553 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1553
    | (have j0 := eq1553 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq1553 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq1790 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1454 x y
       grind)
    | exact superpose eq1454 eq16
    | (have j1 := eq1454 x y
       grind)
    | exact resolve eq16 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454
  have eq1836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1790
       have i₂ := eq1607 x y
       grind)
    | exact superpose eq1607 eq1790
    | (have j1 := eq1607 (σ x) (σ y)
       grind)
    | (have r₁ := eq1790
       have r₂ := eq1607 x y
       grind)
    | (have r₁ := eq1790
       have r₂ := eq1607 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1790
       have r₂ := eq1607 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1790 eq1607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607 eq1790
  have eq1837 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1836
  have eq1841 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1837
       grind)
    | exact superpose eq1837 eq10
    | exact resolve eq10 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837
  have eq1890 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1841
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1841
    | exact resolve eq1841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq1891 : x = y := by grind
  clear eq1890
  have eq1893 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1891
       grind)
    | exact superpose eq1891 eq16
    | exact resolve eq16 eq1891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1891
  have eq1894 : False := by grind
  exact eq1894

/-- `Equation1484`: `x = (y ◇ x) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pyx_pyy_pyx_Equation1484 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1484 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1484.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq26 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq57 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq57 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq58 (σ X0)
       grind)
    | exact superpose eq58 eq15
    | exact resolve eq15 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq58 (τ X0)
       grind)
    | exact superpose eq58 eq18
    | exact resolve eq18 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq63
    | exact resolve eq63 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq60
    | exact resolve eq60 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq58 X0
       grind)
    | exact superpose eq58 eq66
    | exact resolve eq66 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq66
  have eq89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq89
    | (have j0 := eq89 X0 X1
       grind)
    | exact resolve eq89 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq307 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq95 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq336 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq307
    | (have j0 := eq307 X0 X1
       grind)
    | exact resolve eq307 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq307
  have eq341 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq336 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq336 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq336 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq344 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq341 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq341
    | (have j0 := eq341 X0 X1
       grind)
    | exact resolve eq341 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq341
  have eq544 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq344
    | exact resolve eq344 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq551 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq344 (σ X0) X1
       grind)
    | exact superpose eq344 eq15
    | (have j1 := eq344 (σ X0) X1
       grind)
    | exact resolve eq15 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 : G, (k (τ (σ X1)) X0) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X1) X0
       have i₂ := eq344 (σ X0) X1
       grind)
    | exact superpose eq344 eq26
    | (have j1 := eq344 (σ X0) X1
       grind)
    | exact resolve eq26 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq344
  have eq569 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq562
    | (have j0 := eq562 X0 X1
       grind)
    | exact resolve eq562 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq574 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq551
    | (have j0 := eq551 X0 X1
       grind)
    | exact resolve eq551 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq576 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq569 X0 X1
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq569
    | (have j0 := eq569 X0 X1
       grind)
    | exact resolve eq569 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq602 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq544 (τ X1) X0
       grind)
    | exact superpose eq544 eq17
    | (have j1 := eq544 (τ X1) X0
       grind)
    | exact resolve eq17 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq544
  have eq1417 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq602
    | exact resolve eq602 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq1475 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1417 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1417
    | (have j0 := eq1417 X0 X1
       grind)
    | exact resolve eq1417 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq5349 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq574 x y
       grind)
    | exact superpose eq574 eq16
    | (have j1 := eq574 x y
       grind)
    | exact resolve eq16 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5396 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq574 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq5444 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq5349
       have i₂ := eq1475 y x
       grind)
    | exact superpose eq1475 eq5349
    | (have j1 := eq1475 y x
       grind)
    | (have r₁ := eq5349
       have r₂ := eq1475 y x
       grind)
    | exact resolve eq5349 eq1475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349
  have eq5445 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5444
  have eq5589 : x ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq5445
       grind)
    | exact superpose eq5445 eq12
    | (have j0 := eq12 x x
       grind)
    | exact resolve eq12 eq5445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5590 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq5445
       grind)
    | exact superpose eq5445 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5445
       grind)
    | exact resolve eq13 eq5445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5445
  have eq5598 : (k y x) = (M.op x x) ∨ x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5590
  have eq5599 : (k y x) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5589
       have r₂ := eq5598
       grind)
    | exact resolve eq5589 eq5598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5589 eq5598
  have eq5610 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq328 x y
       have i₂ := eq5599
       grind)
    | exact superpose eq5599 eq328
    | (have j0 := eq328 x y
       grind)
    | exact resolve eq328 eq5599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq5622 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5610
  have eq5623 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5622
  have eq5672 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq576 x y
       have i₂ := eq5623
       grind)
    | exact superpose eq5623 eq576
    | (have j0 := eq576 x y
       grind)
    | exact resolve eq576 eq5623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq5682 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq5623
       grind)
    | exact superpose eq5623 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq5623
       grind)
    | exact resolve eq12 eq5623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5690 : (σ x) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5623
  have eq5691 : (σ x) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq5682
  have eq5694 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq5691
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5691
    | exact resolve eq5691 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5691
  have eq5698 : (k y x) = (τ (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5672
       have r₂ := eq5690
       grind)
    | exact resolve eq5672 eq5690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5672
  have eq5704 : x = (k y x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5698
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5698
    | exact resolve eq5698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5698
  have eq5710 : x = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5599
       have i₂ := eq5704
       grind)
    | exact superpose eq5704 eq5599
    | exact resolve eq5599 eq5704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5704
  have eq5740 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq5710
  have eq5877 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq5740
       grind)
    | exact superpose eq5740 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq5740
       grind)
    | exact resolve eq12 eq5740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5878 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq5740
       grind)
    | exact superpose eq5740 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq5740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740
  have eq5888 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq5878
       have r₂ := eq69 x
       grind)
    | exact resolve eq5878 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5878
  have eq5889 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5877
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5877
    | exact resolve eq5877 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5877
  have eq5892 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5888
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5888
    | exact resolve eq5888 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5888
  have eq5893 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5892
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq5892
    | exact resolve eq5892 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5892
  have eq5894 : x = (M.op x x) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5893
       have r₂ := eq5889
       grind)
    | exact resolve eq5893 eq5889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5889 eq5893
  have eq6074 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5690
       have i₂ := eq5894
       grind)
    | exact superpose eq5894 eq5690
    | exact resolve eq5690 eq5894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5690 eq5894
  have eq6075 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq6074
  have eq6198 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq5694
       grind)
    | exact superpose eq5694 eq12
    | exact resolve eq12 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6199 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq5694
       grind)
    | exact superpose eq5694 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq5694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5694
  have eq6209 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq6199
       have r₂ := eq69 x
       grind)
    | exact resolve eq6199 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6199
  have eq6210 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq6198
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6198
    | exact resolve eq6198 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6198
  have eq6213 : (σ (k y x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq6209
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6209
    | exact resolve eq6209 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6209
  have eq6214 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq6213
       have i₂ := eq69 x
       grind)
    | exact superpose eq69 eq6213
    | exact resolve eq6213 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq6213
  have eq6215 : (σ x) = (σ (k y x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq6214
       have r₂ := eq6210
       grind)
    | exact resolve eq6214 eq6210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6210 eq6214
  have eq6324 : (σ x) ≠ (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by grind
  clear eq6215
  have eq7224 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5396 x y
       have i₂ := eq5599
       grind)
    | exact superpose eq5599 eq5396
    | (have j0 := eq5396 x y
       grind)
    | exact resolve eq5396 eq5599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5396 eq5599
  have eq7251 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7224
  have eq7252 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq7251
  have eq7337 : (σ x) = (σ (M.op x x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq6075
       have i₂ := eq7252
       grind)
    | exact superpose eq7252 eq6075
    | exact resolve eq6075 eq7252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6075
  have eq7338 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7252
       grind)
    | exact superpose eq7252 eq16
    | exact resolve eq16 eq7252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7252
  have eq7361 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq7337
       have r₂ := eq6324
       grind)
    | exact resolve eq7337 eq6324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6324 eq7337
  have eq7500 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq1475 y x
       have i₂ := eq7361
       grind)
    | exact superpose eq7361 eq1475
    | (have j0 := eq1475 y x
       grind)
    | exact resolve eq1475 eq7361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475 eq7361
  have eq7578 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq7500
       have r₂ := eq7338
       grind)
    | exact resolve eq7500 eq7338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7500
  have eq7733 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq7338
       have i₂ := eq7578
       grind)
    | exact superpose eq7578 eq7338
    | exact resolve eq7338 eq7578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7338 eq7578
  have eq7746 : False := by grind
  exact eq7746

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq39
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq44 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq40
    | exact resolve eq40 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq40
  have eq82 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86 X0 X1
       have i₂ := eq42 X1
       grind)
    | exact superpose eq42 eq86
    | (have j0 := eq86 X0 X1
       grind)
    | exact resolve eq86 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq93
  have eq468 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq513 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq468 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq468
    | (have j0 := eq468 X0 X1
       grind)
    | exact resolve eq468 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq468
  have eq519 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq513 X0 X1
       have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq513 X1 (τ X1)
       have r₂ := eq82 (τ X1) X1
       grind)
    | (have r₁ := eq513 X1 X0
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq513 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq513
  have eq523 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq519 X0 X1
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq519
    | (have j0 := eq519 X0 X1
       grind)
    | exact resolve eq519 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq519
  have eq928 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq523 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq523
    | exact resolve eq523 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq1024 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq928 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq928 X0 X1
       grind)
    | exact superpose eq928 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq928 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq928 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq928 X1 X1
       grind)
    | exact resolve eq12 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq928 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq928 X0 X1
       grind)
    | exact superpose eq928 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq928 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq928 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq928 X0 X1
       grind)
    | exact resolve eq13 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1070 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1025 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1084 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1024 X0 X1
       have j1 := eq1070 X0 X1
       grind)
    | (have r₁ := eq1024 X0 X1
       have r₂ := eq1070 X0 X1
       grind)
    | (have r₁ := eq1024 X1 X0
       have r₂ := eq1070 X0 X1
       grind)
    | exact resolve eq1024 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024 eq1070
  have eq1170 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1084 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1176 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1170 X0 X1
       have j1 := eq928 X1 X0
       grind)
    | (have r₁ := eq1170 X0 X0
       have r₂ := eq928 X0 X0
       grind)
    | (have r₁ := eq1170 X1 X0
       have r₂ := eq928 X0 X1
       grind)
    | exact resolve eq1170 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928 eq1170
  have eq1304 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1176 (σ X1) (σ X0)
       grind)
    | exact superpose eq1176 eq15
    | exact resolve eq15 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1327 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1304 X0 X1
       have i₂ := eq1176 X1 X0
       grind)
    | exact superpose eq1176 eq1304
    | exact resolve eq1304 eq1176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1176 eq1304
  have eq1920 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1327 x y
       grind)
    | exact superpose eq1327 eq16
    | (have r₁ := eq16
       have r₂ := eq1327 x y
       grind)
    | exact resolve eq16 eq1327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1327
  have eq1959 : False := by grind
  exact eq1959

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxy_pyx_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
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
  have eq89 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq499 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq500 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq516 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq500 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq521 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq516 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq516 X1 X1
       have r₂ := eq12 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq516 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq516 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq522 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq499 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq499 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq499 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499
  have eq530 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq521 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq521
    | (have j0 := eq521 X0 X1
       grind)
    | exact resolve eq521 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq531 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq530 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq532 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq522
    | (have j0 := eq522 X0 X1
       grind)
    | exact resolve eq522 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq533 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq532 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq538 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq533 X0 X1
       have j1 := eq531 X0 X1
       grind)
    | (have r₁ := eq533 X0 X1
       have r₂ := eq531 X0 X1
       grind)
    | exact resolve eq533 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq533
  have eq539 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq538 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq538
    | exact resolve eq538 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq538 x y
       grind)
    | exact superpose eq538 eq16
    | exact resolve eq16 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq657 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq539 X0 (τ X1)
       grind)
    | exact superpose eq539 eq18
    | exact resolve eq18 eq539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq539
  have eq682 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq657 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq657
    | exact resolve eq657 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq694 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq682 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq682
    | exact resolve eq682 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq721 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq550
       have i₂ := eq694 x y
       grind)
    | exact superpose eq694 eq550
    | exact resolve eq550 eq694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq694
  have eq722 : False := by grind
  exact eq722

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq85 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq287 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq85 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq85 X0 X1
       grind)
    | exact resolve eq13 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq298 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq299 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq287 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq300 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq299 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq302 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq300 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq300
    | (have j0 := eq300 X0 X1
       grind)
    | exact resolve eq300 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300
  have eq306 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq302 X0 X1
       have j1 := eq298 X0 X1
       grind)
    | (have r₁ := eq302 X0 X1
       have r₂ := eq298 X0 X1
       grind)
    | (have r₁ := eq302 (k X0 X1) X0
       have r₂ := eq298 X0 X1
       grind)
    | (have r₁ := eq302 X0 X0
       have r₂ := eq298 X0 X0
       grind)
    | exact resolve eq302 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq302
  have eq963 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq306 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq306
    | exact resolve eq306 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq971 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq1002 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq963 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq963
    | (have j0 := eq963 X0 X1
       grind)
    | exact resolve eq963 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq963
  have eq1004 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1002 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1002
    | exact resolve eq1002 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1063 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1004 (τ X0) X1
       grind)
    | exact superpose eq1004 eq18
    | (have j1 := eq1004 (τ X0) X1
       grind)
    | exact resolve eq18 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1004
  have eq1887 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1063 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1063
    | exact resolve eq1063 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1936 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1887 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1887
    | (have j0 := eq1887 X0 X1
       grind)
    | exact resolve eq1887 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887
  have eq2598 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq971
       have i₂ := eq1936 x y
       grind)
    | exact superpose eq1936 eq971
    | (have j1 := eq1936 (σ x) (σ y)
       grind)
    | (have r₁ := eq971
       have r₂ := eq1936 x y
       grind)
    | exact resolve eq971 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2599 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2598
  have eq2645 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2599
  have eq2847 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq971
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq971
    | exact resolve eq971 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq2645
  have eq2848 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2847
  have eq2849 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq2848
  have eq2902 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq2849
  have eq2904 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq2902
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq2902
    | exact resolve eq2902 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2902
  have eq2965 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2904
       grind)
    | exact superpose eq2904 eq16
    | exact resolve eq16 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904
  have eq3014 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2965
       have i₂ := eq1936 x y
       grind)
    | exact superpose eq1936 eq2965
    | (have j1 := eq1936 x y
       grind)
    | (have r₁ := eq2965
       have r₂ := eq1936 x y
       grind)
    | exact resolve eq2965 eq1936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1936
  have eq3015 : x = (M.op y y) := by grind
  clear eq3014
  have eq3265 : (M.op x y) = (k x y) := by grind
  clear eq3015
  have eq3314 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2965
       have i₂ := eq3265
       grind)
    | exact superpose eq3265 eq2965
    | exact resolve eq2965 eq3265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2965 eq3265
  have eq3317 : False := by grind
  exact eq3317

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pyx_x_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq112
    | exact resolve eq112 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq113
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq113
    | exact resolve eq113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq869 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq11610 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11611 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11610
    | exact resolve eq11610 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11610
  have eq11622 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq11611
       have r₂ := eq28
       grind)
    | exact resolve eq11611 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11611
  have eq11624 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11622
    | exact resolve eq11622 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11622
  have eq11634 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq11624
  have eq11672 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq11634
    | exact resolve eq11634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11634
  have eq11829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq11672 eq114
    | exact resolve eq114 eq11672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11672
  have eq11837 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11829
  have eq11839 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11837
       have r₂ := eq28
       grind)
    | exact resolve eq11837 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11837
  have eq11850 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11839
  have eq11888 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11850
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq11850
    | exact resolve eq11850 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11850
  have eq11891 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11888
       grind)
    | exact superpose eq11888 eq73
    | exact resolve eq73 eq11888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11888
  have eq11905 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq11891
    | exact resolve eq11891 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11891
  have eq11918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11905 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11918
    | exact resolve eq11918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11918
  have eq11932 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11921
       have r₂ := eq28
       grind)
    | exact resolve eq11921 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11921
  have eq11934 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq11932
    | exact resolve eq11932 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11932
  have eq11935 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11934
  have eq11946 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11935
  have eq11984 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq11946
    | exact resolve eq11946 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11946
  have eq11998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11984 eq11905
    | exact resolve eq11905 eq11984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11905 eq11984
  have eq12000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11998
  have eq12004 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12000
       have r₂ := eq28
       grind)
    | exact resolve eq12000 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12000
  have eq12006 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12004 eq28
    | exact resolve eq28 eq12004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12009 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12004 eq77
    | (have r₁ := eq77
       have r₂ := eq12004
       grind)
    | exact resolve eq77 eq12004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq12004
  have eq12040 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12009
  have eq15812 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12040 eq114
    | exact resolve eq114 eq12040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15829 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq15812
  have eq15843 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15829
       have r₂ := eq12006
       grind)
    | exact resolve eq15829 eq12006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15829
  have eq16431 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq15843
  have eq16484 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq16431
    | exact resolve eq16431 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16431
  have eq16557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16484 eq114
    | exact resolve eq114 eq16484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq16484
  have eq16570 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq16557
  have eq16574 : y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16570
       have r₂ := eq28
       grind)
    | exact resolve eq16570 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16570
  have eq16585 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq16574
  have eq16635 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16585
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16585
    | exact resolve eq16585 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16585
  have eq16640 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq16635
       grind)
    | exact superpose eq16635 eq73
    | exact resolve eq73 eq16635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16635
  have eq16656 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq16640
    | exact resolve eq16640 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16640
  have eq16674 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16656 eq12040
    | exact resolve eq12040 eq16656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12040
  have eq16679 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq16674
  have eq16687 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq16679
       have r₂ := eq12006
       grind)
    | exact resolve eq16679 eq12006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12006 eq16679
  have eq16714 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq16687
  have eq16767 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq16714
    | exact resolve eq16714 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16714
  have eq16799 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16767 eq16656
    | exact resolve eq16656 eq16767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16656 eq16767
  have eq16802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq16799
  have eq16810 : y = (M.op x y) := by
    first
    | (have r₁ := eq16802
       have r₂ := eq28
       grind)
    | exact resolve eq16802 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16802
  have eq16812 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq16810 eq21
    | exact resolve eq21 eq16810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq16819 : y ≠ y ∨ y = (M.op x x) ∨ y = (k y x) := by
    first
    | exact superpose eq16810 eq76
    | (have r₁ := eq76
       have r₂ := eq16810
       grind)
    | exact resolve eq76 eq16810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq16899 : y = (k y x) ∨ y = (M.op x x) := by grind
  clear eq16819
  have eq16950 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16812
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq16812
    | exact resolve eq16812 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16812
  have eq16979 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq16950 eq27
    | exact resolve eq27 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq22797 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq16899
       grind)
    | exact superpose eq16899 eq73
    | exact resolve eq73 eq16899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22807 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq869 x y
       have i₂ := eq16899
       grind)
    | exact superpose eq16899 eq869
    | (have j0 := eq869 x y
       grind)
    | exact resolve eq869 eq16899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16899
  have eq22810 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq22807
  have eq22817 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22810
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22810
    | exact resolve eq22810 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22810
  have eq22825 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16950 eq22797
    | exact resolve eq22797 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22797
  have eq22827 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16950 eq22817
    | exact resolve eq22817 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22817
  have eq22835 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22825
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22825
    | exact resolve eq22825 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22825
  have eq22836 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22827
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22827
    | exact resolve eq22827 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22827
  have eq22843 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16950 eq22835
    | exact resolve eq22835 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22835
  have eq22844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16979 eq22836
    | exact resolve eq22836 eq16979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22836
  have eq22846 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq22844
       have r₂ := eq28
       grind)
    | exact resolve eq22844 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22844
  have eq22848 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22846
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq22846
    | exact resolve eq22846 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22846
  have eq22850 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq22848
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq22848
    | exact resolve eq22848 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22848
  have eq22852 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16950 eq22850
    | exact resolve eq22850 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22850
  have eq22919 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by grind
  clear eq22852
  have eq22987 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq16979 eq22919
    | exact resolve eq22919 eq16979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22919
  have eq23750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq22987 eq22843
    | exact resolve eq22843 eq22987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22843 eq22987
  have eq23754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq23750
  have eq23756 : y = (M.op x x) := by
    first
    | (have r₁ := eq23754
       have r₂ := eq28
       grind)
    | exact resolve eq23754 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23754
  have eq23781 : (M.op x y) = (k y x) := by grind
  clear eq23756
  have eq23847 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq23781
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq23781
    | exact resolve eq23781 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq23781
  have eq23860 : y = (k y x) := by
    first
    | exact superpose eq16810 eq23847
    | exact resolve eq23847 eq16810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16810 eq23847
  have eq23867 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq23860
       grind)
    | exact superpose eq23860 eq73
    | exact resolve eq73 eq23860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq23877 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq869 x y
       have i₂ := eq23860
       grind)
    | exact superpose eq23860 eq869
    | (have j0 := eq869 x y
       grind)
    | exact resolve eq869 eq23860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq869 eq23860
  have eq23880 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq23877
  have eq23886 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq23880
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23880
    | exact resolve eq23880 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23880
  have eq23894 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq16950 eq23867
    | exact resolve eq23867 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23867
  have eq23895 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16950 eq23886
    | exact resolve eq23886 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23886
  have eq23903 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq23894
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23894
    | exact resolve eq23894 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23894
  have eq23904 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq23895
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23895
    | exact resolve eq23895 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23895
  have eq23911 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq16950 eq23903
    | exact resolve eq23903 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23903
  have eq23912 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16979 eq23904
    | exact resolve eq23904 eq16979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23904
  have eq23914 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq23912
       have r₂ := eq28
       grind)
    | exact resolve eq23912 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23912
  have eq23916 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq23914
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23914
    | exact resolve eq23914 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq23914
  have eq23918 : (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq23916
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq23916
    | exact resolve eq23916 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq23916
  have eq23920 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16950 eq23918
    | exact resolve eq23918 eq16950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16950 eq23918
  have eq24358 : (k (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq23920
  have eq24425 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq16979 eq24358
    | exact resolve eq24358 eq16979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16979 eq24358
  have eq24432 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23911 eq24425
    | exact resolve eq24425 eq23911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23911 eq24425
  have eq24433 : False := by grind
  exact eq24433

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pyx_y_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq23
    | exact resolve eq23 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) := by
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
  have eq170 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq16
    | (have j1 := eq58 y x
       grind)
    | exact resolve eq16 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq313 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq63 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq332 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq335 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq332 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq332
    | (have j0 := eq332 X0
       grind)
    | exact resolve eq332 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq341 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq313 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq313
    | (have j0 := eq313 X0 X1
       grind)
    | exact resolve eq313 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq456 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq170
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq170
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq170 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq457 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq456
  have eq970 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq335 X0
       grind)
    | exact superpose eq335 eq10
    | (have j1 := eq335 X0
       grind)
    | exact resolve eq10 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq1294 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    grind
  clear eq970
  have eq1321 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1294 X0
       have i₂ := eq36 X0 X0
       grind)
    | exact superpose eq36 eq1294
    | (have j0 := eq1294 X0
       grind)
    | exact resolve eq1294 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1294
  have eq1322 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1321 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1321
  have eq1326 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq1322 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1322
    | exact resolve eq1322 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1370 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1326 X0
       have i₂ := eq23 (σ X0) X0
       grind)
    | exact superpose eq23 eq1326
    | exact resolve eq1326 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1326
  have eq1372 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1370 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1370
    | exact resolve eq1370 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1370
  have eq1489 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1372 (σ X0)
       grind)
    | exact superpose eq1372 eq15
    | exact resolve eq15 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1509 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1489 X0
       have i₂ := eq1372 X0
       grind)
    | exact superpose eq1372 eq1489
    | exact resolve eq1489 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1372 eq1489
  have eq1578 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq1609 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1578 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq1578
    | exact resolve eq1578 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1578
  have eq1618 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq1609
  have eq2854 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq1509 X0
       grind)
    | exact superpose eq1509 eq181
    | (have j0 := eq181 X0 X1
       grind)
    | exact resolve eq181 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq16629 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq457
       have i₂ := eq1509 x
       grind)
    | exact superpose eq1509 eq457
    | exact resolve eq457 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq16664 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq16629
       grind)
    | exact superpose eq16629 eq10
    | exact resolve eq10 eq16629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16629
  have eq16719 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16664
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq16664
    | exact resolve eq16664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16664
  have eq16720 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq16719
  have eq44836 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16720
       grind)
    | exact superpose eq16720 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16720
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq16720
       grind)
    | exact resolve eq13 eq16720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16720
  have eq44919 : x ≠ x ∨ y = (M.op x x) ∨ x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44836
  have eq44920 : x = (k y x) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44919
  have eq44925 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2854 x y
       have i₂ := eq44920
       grind)
    | exact superpose eq44920 eq2854
    | (have j0 := eq2854 x y
       grind)
    | exact resolve eq2854 eq44920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854 eq44920
  have eq44935 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by grind
  clear eq44925
  have eq44936 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq44935
  have eq173545 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44936
       grind)
    | exact superpose eq44936 eq16
    | exact resolve eq16 eq44936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173581 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq44936
       grind)
    | exact superpose eq44936 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq44936
       grind)
    | exact resolve eq13 eq44936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44936
  have eq173700 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq173581
  have eq173709 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq173700
       have i₂ := eq1509 x
       grind)
    | exact superpose eq1509 eq173700
    | exact resolve eq173700 eq1509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1509 eq173700
  have eq173710 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x x) := by grind
  clear eq173709
  have eq173714 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq173710
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq173710
    | exact resolve eq173710 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173710
  have eq175648 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq1618 x
       have i₂ := eq173714
       grind)
    | exact superpose eq173714 eq1618
    | exact resolve eq1618 eq173714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173714
  have eq175912 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq175648
       have r₂ := eq16
       grind)
    | exact resolve eq175648 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175648
  have eq176528 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq341 y x
       have i₂ := eq175912
       grind)
    | exact superpose eq175912 eq341
    | (have j0 := eq341 y x
       grind)
    | exact resolve eq341 eq175912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341 eq175912
  have eq176864 : x = (M.op x y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq176528
       have r₂ := eq173545
       grind)
    | exact resolve eq176528 eq173545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176528
  have eq180125 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq173545
       have i₂ := eq176864
       grind)
    | exact superpose eq176864 eq173545
    | exact resolve eq173545 eq176864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173545 eq176864
  have eq180249 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq180125
  have eq180250 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq180249
  have eq181220 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1618 x
       have i₂ := eq180250
       grind)
    | exact superpose eq180250 eq1618
    | exact resolve eq1618 eq180250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180250
  have eq181486 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq181220
       have r₂ := eq16
       grind)
    | exact resolve eq181220 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181220
  have eq182523 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq181486
       grind)
    | exact superpose eq181486 eq10
    | exact resolve eq10 eq181486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181486
  have eq182849 : y = (M.op x x) := by
    first
    | (have i₁ := eq182523
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq182523
    | exact resolve eq182523 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182523
  have eq183739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1618 x
       have i₂ := eq182849
       grind)
    | exact superpose eq182849 eq1618
    | exact resolve eq1618 eq182849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1618 eq182849
  have eq184005 : False := by grind
  exact eq184005
