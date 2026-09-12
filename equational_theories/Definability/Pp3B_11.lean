import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1630`: `x = (x ◇ x) ◇ ((x ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxx_y_pxy_Equation1630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) X1)) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq20 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op (M.op X0 X0) x)
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq198 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq789 : ∀ X0 X1 : G, (σ (σ (k X0 X1))) ≠ (σ (σ X1)) ∨ (σ (σ X1)) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (σ (σ X0)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq198 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq198
    | (have j0 := eq198 (σ X0) (σ X1)
       grind)
    | exact resolve eq198 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq855 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (M.op (τ X0) (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (τ X0)
       have i₂ := eq76 X1 X0
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 X1 (τ X0)
       have j1 := eq76 X1 X0
       grind)
    | (have r₁ := eq13 X0 (τ X1)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) (τ X1)
       have r₂ := eq76 (τ X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op (τ X1) (τ X1))
       have r₂ := eq76 (M.op X0 (M.op (τ X1) (τ X1))) X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq76 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq862 : ∀ X0 : G, (k (σ (τ X0)) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq861 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq864 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (k X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (k (σ X1) X0) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq855 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq865 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op X1 (τ X0))) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (k X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq864 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864
  have eq867 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq862 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq862
    | (have j0 := eq862 X0
       grind)
    | exact resolve eq862 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq881 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq867 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq867
    | exact resolve eq867 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq903 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq881 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq881
    | (have j0 := eq881 X0
       grind)
    | exact resolve eq881 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq909 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq903 X0
       grind)
    | exact superpose eq903 eq9
    | (have j1 := eq903 X0
       grind)
    | exact resolve eq9 eq903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : ∀ X0 X1 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq909 X0 X1
       grind)
    | exact superpose eq909 eq10
    | (have j1 := eq909 X0 X1
       grind)
    | exact resolve eq10 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1179 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1140 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1140
    | (have j0 := eq1140 X0 X1
       grind)
    | exact resolve eq1140 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1187 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq1179 X0 (M.op X0 x)
       have i₂ := eq1179 X0 x
       grind)
    | exact superpose eq1179 eq1179
    | (have j0 := eq1179 X0 x
       have j1 := eq1179 X0 x
       grind)
    | exact resolve eq1179 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq1229 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1187 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1187
  have eq1344 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq1229
  have eq1365 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1344 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq1418 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1365 (σ X0)
       grind)
    | exact superpose eq1365 eq15
    | exact resolve eq15 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1425 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq1365 (τ X0)
       grind)
    | exact superpose eq1365 eq38
    | exact resolve eq38 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1441 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1425 X0
       have i₂ := eq1365 X0
       grind)
    | exact superpose eq1365 eq1425
    | exact resolve eq1425 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq1447 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1418 X0
       have i₂ := eq1365 X0
       grind)
    | exact superpose eq1365 eq1418
    | exact resolve eq1418 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1607 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0)
       have i₂ := eq1447 X0
       grind)
    | exact superpose eq1447 eq20
    | exact resolve eq20 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10740 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq865 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq865
    | exact resolve eq865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq10895 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10740 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq10740
    | (have j0 := eq10740 X0 X1
       grind)
    | exact resolve eq10740 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10740
  have eq11071 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq10895 X1 X0
       grind)
    | exact superpose eq10895 eq10
    | (have j1 := eq10895 X1 X0
       grind)
    | exact resolve eq10 eq10895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10895
  have eq11127 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11071 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq11071
    | (have j0 := eq11071 X0 X1
       grind)
    | exact resolve eq11071 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11071
  have eq11249 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = (M.op X1 X1) ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X0 X1
       have i₂ := eq11127 (σ X0) X1
       grind)
    | exact superpose eq11127 eq35
    | (have j1 := eq11127 (σ X0) X1
       grind)
    | exact resolve eq35 eq11127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq11127
  have eq22672 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X1) X0
       have i₂ := eq11249 X1 (σ X0)
       grind)
    | exact superpose eq11249 eq25
    | (have j1 := eq11249 X1 (σ X0)
       grind)
    | exact resolve eq25 eq11249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq11249
  have eq22760 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22672 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq22672
    | (have j0 := eq22672 X0 X1
       grind)
    | exact resolve eq22672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22672
  have eq22858 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22760 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22760
    | (have j0 := eq22760 X0 X1
       grind)
    | exact resolve eq22760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22760
  have eq22938 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22858 X0 X1
       have i₂ := eq1447 X0
       grind)
    | exact superpose eq1447 eq22858
    | (have j0 := eq22858 X0 X1
       grind)
    | exact resolve eq22858 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22858
  have eq22993 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22938 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq22938
    | (have j0 := eq22938 X0 X1
       grind)
    | exact resolve eq22938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22938
  have eq23639 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (σ (M.op X1 X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq22993 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22993
    | (have j0 := eq22993 X1 (τ X0)
       grind)
    | exact resolve eq22993 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23754 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq22993 X1 X0
       grind)
    | exact superpose eq22993 eq11
    | (have j1 := eq22993 X1 X0
       grind)
    | exact resolve eq11 eq22993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22993
  have eq24301 : ∀ X0 X1 : G, (τ X1) = (τ (k X0 X1)) ∨ (σ (M.op (τ X1) (τ X1))) = X0 ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq23639 X1 (τ X0)
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq23639
    | (have j0 := eq23639 X0 (τ X1)
       grind)
    | exact resolve eq23639 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23639
  have eq24567 : ∀ X0 X1 : G, (σ (τ (M.op X1 X1))) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24301 X0 X1
       have i₂ := eq1441 X1
       grind)
    | exact superpose eq1441 eq24301
    | (have j0 := eq24301 X0 X1
       grind)
    | exact resolve eq24301 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24301
  have eq24673 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op X0 (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24567 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq24567
    | (have j0 := eq24567 X0 X1
       grind)
    | exact resolve eq24567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24567
  have eq24758 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24673 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq24673
    | (have j0 := eq24673 X0 X1
       grind)
    | exact resolve eq24673 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24673
  have eq25182 : ∀ X0 X1 : G, (τ X1) ≠ (τ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (τ X1) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq24758 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24758
  have eq25345 : ∀ X0 X1 : G, (σ (σ (τ X1))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq789 (τ X0) (τ X1)
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq789
    | (have j0 := eq789 (τ X0) (τ X1)
       grind)
    | exact resolve eq789 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq789
  have eq25435 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X1))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25345 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq25345
    | (have j0 := eq25345 X0 X1
       grind)
    | exact resolve eq25345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25345
  have eq25486 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X0))) (σ (σ (τ X1)))) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25435 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq25435
    | (have j0 := eq25435 X0 X1
       grind)
    | exact resolve eq25435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25435
  have eq25533 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (σ (τ X0))) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25486 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25486
    | (have j0 := eq25486 X0 X1
       grind)
    | exact resolve eq25486 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25486
  have eq25569 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (σ (τ X0))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25533 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25533
    | (have j0 := eq25533 X0 X1
       grind)
    | exact resolve eq25533 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25533
  have eq25597 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (M.op (σ (τ X1)) (σ (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25569 X0 X1
       have i₂ := eq1447 (σ (τ X1))
       grind)
    | exact superpose eq1447 eq25569
    | (have j0 := eq25569 X0 X1
       grind)
    | exact resolve eq25569 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25569
  have eq25624 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (M.op (τ X1) (τ X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25597 X0 X1
       have i₂ := eq1447 (τ X1)
       grind)
    | exact superpose eq1447 eq25597
    | (have j0 := eq25597 X0 X1
       grind)
    | exact resolve eq25597 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25597
  have eq25646 : ∀ X0 X1 : G, (σ (σ (τ X0))) = (σ (σ (τ (M.op X1 X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25624 X0 X1
       have i₂ := eq1441 X1
       grind)
    | exact superpose eq1441 eq25624
    | (have j0 := eq25624 X0 X1
       grind)
    | exact resolve eq25624 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441 eq25624
  have eq25662 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (τ X0))) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) ≠ (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25646 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq25646
    | (have j0 := eq25646 X0 X1
       grind)
    | exact resolve eq25646 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25646
  have eq25673 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25662 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25662
    | (have j0 := eq25662 X0 X1
       grind)
    | exact resolve eq25662 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25662
  have eq28278 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23754 x y
       grind)
    | exact superpose eq23754 eq16
    | (have j1 := eq23754 x y
       grind)
    | exact resolve eq16 eq23754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23754
  have eq29084 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq28278
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq28278
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq28278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28278
  have eq29090 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq29084
  have eq29091 : y = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq29090
  have eq29653 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ (k x y)) = (τ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq25182 x y
       have i₂ := eq29091
       grind)
    | exact superpose eq29091 eq25182
    | (have j0 := eq25182 x y
       grind)
    | exact resolve eq25182 eq29091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25182
  have eq29658 : (τ y) ≠ (τ y) ∨ x = (M.op y y) ∨ (τ (k x y)) = (τ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq29653
  have eq29659 : x = (M.op y y) ∨ (τ (k x y)) = (τ y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq29658
  have eq29685 : x = y ∨ (σ x) = (σ (k y y)) ∨ (τ (k x y)) = (τ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq903 y
       have i₂ := eq29659
       grind)
    | exact superpose eq29659 eq903
    | exact resolve eq903 eq29659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29659
  have eq29742 : (σ x) = (σ (M.op y y)) ∨ x = y ∨ (τ (k x y)) = (τ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq29685
       have i₂ := eq1365 y
       grind)
    | exact superpose eq1365 eq29685
    | exact resolve eq29685 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29685
  have eq29743 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ (τ (k x y)) = (τ y) := by grind
  clear eq29742
  have eq30036 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ (τ (k x y)) = (τ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29743
       grind)
    | exact superpose eq29743 eq16
    | exact resolve eq16 eq29743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29743
  have eq30050 : (σ x) = (σ (M.op y y)) ∨ (τ (k x y)) = (τ y) := by
    first
    | (have r₁ := eq30036
       have r₂ := eq1447 x
       grind)
    | exact resolve eq30036 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30036
  have eq30069 : (σ y) = (M.op (σ x) (σ y)) ∨ (τ (k x y)) = (τ y) := by
    first
    | (have i₁ := eq1607 y
       have i₂ := eq30050
       grind)
    | exact superpose eq30050 eq1607
    | exact resolve eq1607 eq30050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30079 : (M.op y y) = (τ (σ x)) ∨ (τ (k x y)) = (τ y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq30050
       grind)
    | exact superpose eq30050 eq10
    | exact resolve eq10 eq30050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30050
  have eq30170 : x = (M.op y y) ∨ (τ (k x y)) = (τ y) := by
    first
    | (have i₁ := eq30079
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30079
    | exact resolve eq30079 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30079
  have eq30725 : y = (M.op x y) ∨ (τ (k x y)) = (τ y) := by
    first
    | (have i₁ := eq20 y
       have i₂ := eq30170
       grind)
    | exact superpose eq30170 eq20
    | exact resolve eq20 eq30170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30170
  have eq32049 : (σ (M.op x y)) ≠ (σ y) ∨ (τ (k x y)) = (τ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30069
       grind)
    | exact superpose eq30069 eq16
    | exact resolve eq16 eq30069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30069
  have eq32063 : (σ y) ≠ (σ y) ∨ (τ (k x y)) = (τ y) ∨ (τ (k x y)) = (τ y) := by
    first
    | (have i₁ := eq32049
       have i₂ := eq30725
       grind)
    | exact superpose eq30725 eq32049
    | exact resolve eq32049 eq30725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30725 eq32049
  have eq32066 : (σ y) ≠ (σ y) ∨ (τ (k x y)) = (τ y) := by grind
  clear eq32063
  have eq32067 : (τ (k x y)) = (τ y) := by grind
  clear eq32066
  have eq32138 : (k x y) = (σ (τ y)) := by
    first
    | (have i₁ := eq11 (k x y)
       have i₂ := eq32067
       grind)
    | exact superpose eq32067 eq11
    | exact resolve eq11 eq32067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32067
  have eq32300 : y = (k x y) := by
    first
    | (have i₁ := eq32138
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq32138
    | exact resolve eq32138 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32138
  have eq32324 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq25673 x y
       have i₂ := eq32300
       grind)
    | exact superpose eq32300 eq25673
    | (have j0 := eq25673 x y
       grind)
    | exact resolve eq25673 eq32300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25673 eq32300
  have eq32325 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq32324
  have eq34402 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32325
       grind)
    | exact superpose eq32325 eq16
    | exact resolve eq16 eq32325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32325
  have eq34425 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq34402
       have i₂ := eq29091
       grind)
    | exact superpose eq29091 eq34402
    | exact resolve eq34402 eq29091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29091 eq34402
  have eq34426 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq34425
  have eq34427 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq34426
  have eq34674 : x = y ∨ (σ x) = (σ (k y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq903 y
       have i₂ := eq34427
       grind)
    | exact superpose eq34427 eq903
    | exact resolve eq903 eq34427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903 eq34427
  have eq34744 : (σ x) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq34674
       have i₂ := eq1365 y
       grind)
    | exact superpose eq1365 eq34674
    | exact resolve eq34674 eq1365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365 eq34674
  have eq34745 : x = y ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq34744
  have eq34776 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34745
       grind)
    | exact superpose eq34745 eq16
    | exact resolve eq16 eq34745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34745
  have eq34826 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq34776
       have r₂ := eq1447 x
       grind)
    | exact resolve eq34776 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1447 eq34776
  have eq34897 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1607 y
       have i₂ := eq34826
       grind)
    | exact superpose eq34826 eq1607
    | exact resolve eq1607 eq34826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq34907 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq34826
       grind)
    | exact superpose eq34826 eq10
    | exact resolve eq10 eq34826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34826
  have eq35010 : x = (M.op y y) := by
    first
    | (have i₁ := eq34907
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq34907
    | exact resolve eq34907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34907
  have eq35043 : y = (M.op x y) := by
    first
    | (have i₁ := eq20 y
       have i₂ := eq35010
       grind)
    | exact superpose eq35010 eq20
    | exact resolve eq20 eq35010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq35010
  have eq37099 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34897
       grind)
    | exact superpose eq34897 eq16
    | exact resolve eq16 eq34897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34897
  have eq37110 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq37099
       have i₂ := eq35043
       grind)
    | exact superpose eq35043 eq37099
    | exact resolve eq37099 eq35043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35043 eq37099
  have eq37111 : False := by grind
  exact eq37111

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_pyy_pxy_pxx_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (M.op (M.op X2 X3) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) (M.op (M.op X2 X3) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq68
  have eq92 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq9
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op (σ (σ (M.op X0 X0))) (M.op (M.op (σ (σ X0)) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (σ X0) X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq92
    | exact resolve eq92 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq209 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 (M.op X0 (M.op (M.op X1 X2) X2)) X1 X2 x
       have i₂ := eq9 X0 (M.op (M.op X1 X2) X2) x
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq255 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X2)) = (M.op X0 (M.op (M.op X1 X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 (M.op (M.op X1 X3) X3)) X1 X2
       have i₂ := eq209 X0 X1 X3
       grind)
    | exact superpose eq209 eq9
    | exact resolve eq9 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op (M.op X2 X3) X3)) (M.op (M.op X2 X4) X4))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq62 (M.op X0 (M.op (M.op X2 X3) X3)) X1 X2 X4
       have i₂ := eq209 X0 X2 X3
       grind)
    | exact superpose eq209 eq62
    | exact resolve eq62 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq209
  have eq1015 : ∀ X0 X1 X2 X3 : G, (σ (σ X0)) = (M.op (σ (σ (M.op X0 X0))) (M.op (M.op (σ (σ X0)) (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X3) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq139 X0 (M.op (M.op X1 X3) X3)
       have i₂ := eq255 (σ (σ X0)) X1 X3 X2
       grind)
    | (have i₁ := eq139 X0 (M.op (M.op X1 X3) X3)
       have i₂ := eq255 (σ (σ X0)) X1 X2 X3
       grind)
    | exact superpose eq255 eq139
    | exact resolve eq139 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq255
  have eq7978 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq8037 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7978 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq7978
    | (have j0 := eq7978 X0 X1
       grind)
    | exact resolve eq7978 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7978
  have eq15168 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq8037 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq8037 X0 X1
       grind)
    | exact superpose eq8037 eq12
    | (have j1 := eq8037 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq8037 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq8037 X0 X1
       grind)
    | exact resolve eq12 eq8037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8037
  have eq15198 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq15168 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15168
  have eq15202 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15198 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq15198
    | (have j0 := eq15198 X0 X1
       grind)
    | exact resolve eq15198 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15198
  have eq15203 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq15202 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15202
  have eq15276 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X1) (σ X1))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15203 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq15203
    | (have j0 := eq15203 (σ X1) (σ X0)
       grind)
    | exact resolve eq15203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15203
  have eq15405 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op (σ (σ X0)) (σ (σ X1))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15276 X0 X1
       have i₂ := eq79 X1
       grind)
    | exact superpose eq79 eq15276
    | (have j0 := eq15276 X0 X1
       grind)
    | exact resolve eq15276 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15276
  have eq180691 : ∀ X0 X1 X2 X3 X4 : G, (σ (σ X1)) = (M.op (σ (σ (M.op X0 X0))) (M.op (M.op (σ (σ X0)) (M.op (M.op X2 X3) X3)) (M.op (M.op X2 X4) X4))) ∨ (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq308 (σ (σ X0)) (σ (σ X1)) X2 X3 X4
       have i₂ := eq15405 X1 X0
       grind)
    | exact superpose eq15405 eq308
    | (have j1 := eq15405 X1 X0
       grind)
    | exact resolve eq308 eq15405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq15405
  have eq180794 : ∀ X0 X1 : G, (M.op (σ (σ X0)) (σ (σ X1))) = (σ (σ (k X1 X0))) ∨ (σ (σ X0)) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq180691 X0 X1 x x x
       have i₂ := eq1015 X0 x x x
       grind)
    | exact superpose eq1015 eq180691
    | (have j0 := eq180691 X0 X1 x x x
       grind)
    | exact resolve eq180691 eq1015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015 eq180691
  have eq181616 : ∀ X0 X1 : G, (σ (σ (k (τ X0) X1))) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq180794 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq180794
    | exact resolve eq180794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180794
  have eq181900 : ∀ X0 X1 : G, (σ (k X0 (σ X1))) = (M.op (σ (σ X1)) (σ X0)) ∨ (σ X0) = (σ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq181616 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq181616
    | (have j0 := eq181616 X0 X1
       grind)
    | exact resolve eq181616 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq181616
  have eq181933 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq181900 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq181900
    | exact resolve eq181900 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181900
  have eq182232 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq181933 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq181933
    | (have j0 := eq181933 (τ X0) (τ X1)
       grind)
    | exact resolve eq181933 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq182515 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq182232 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq182232
    | (have j0 := eq182232 X0 X1
       grind)
    | exact resolve eq182232 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182232
  have eq182569 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq182515 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq182515
    | (have j0 := eq182515 X0 X1
       grind)
    | exact resolve eq182515 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182515
  have eq182603 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq182569 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq182569
    | (have j0 := eq182569 X0 X1
       grind)
    | exact resolve eq182569 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182569
  have eq182636 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq182603 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq182603
    | (have j0 := eq182603 X0 X1
       grind)
    | exact resolve eq182603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182603
  have eq182653 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182636 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq182636
    | (have j0 := eq182636 X0 X1
       grind)
    | exact resolve eq182636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182636
  have eq182716 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq181933 X0 X1
       have i₂ := eq182653 X1 X0
       grind)
    | exact superpose eq182653 eq181933
    | (have j0 := eq181933 X0 X1
       have j1 := eq182653 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq181933 eq182653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181933 eq182653
  have eq184888 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq182716 x y
       grind)
    | exact superpose eq182716 eq16
    | (have j1 := eq182716 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq182716 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq182716 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq182716 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq182716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182716
  have eq185084 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq184888
  have eq185151 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq185084
       grind)
    | exact superpose eq185084 eq10
    | exact resolve eq10 eq185084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185084
  have eq185406 : x = y ∨ x = y := by
    first
    | (have i₁ := eq185151
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq185151
    | exact resolve eq185151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185151
  have eq185407 : x = y := by grind
  clear eq185406
  have eq185410 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq185407
       grind)
    | exact superpose eq185407 eq16
    | exact resolve eq16 eq185407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185407
  have eq185411 : False := by grind
  exact eq185411

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_y_pyx_y_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq498 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq499 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq498 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq498
    | (have j0 := eq498 (σ X0) (σ X1)
       grind)
    | exact resolve eq498 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq500 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq498 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq498
    | (have j0 := eq498 (τ X0) (τ X1)
       grind)
    | exact resolve eq498 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq641 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq499 X1 X0
       have i₂ := eq498 X1 X0
       grind)
    | exact superpose eq498 eq499
    | (have j0 := eq499 X1 X0
       have j1 := eq498 (σ X1) (σ X0)
       grind)
    | exact resolve eq499 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq500 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq814 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq789 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq789
    | (have j0 := eq789 (σ X1) (σ X0)
       grind)
    | exact resolve eq789 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq824 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq814 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq814
    | (have j0 := eq814 X0 X1
       grind)
    | exact resolve eq814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq826 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq824
    | (have j0 := eq824 X0 X1
       grind)
    | exact resolve eq824 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq827 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq826 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq826
    | (have j0 := eq826 X0 X1
       grind)
    | exact resolve eq826 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq828 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq827 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq827
    | (have j0 := eq827 X0 X1
       grind)
    | exact resolve eq827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq830 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq828 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq828
    | (have j0 := eq828 (σ X0) (σ X1)
       grind)
    | exact resolve eq828 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq9666 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq641 x y
       grind)
    | exact superpose eq641 eq16
    | (have j1 := eq641 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq641 x y
       grind)
    | exact resolve eq16 eq641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641
  have eq9712 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq9666
  have eq9732 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9712
       grind)
    | exact superpose eq9712 eq16
    | exact resolve eq16 eq9712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9736 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq9712
       grind)
    | exact superpose eq9712 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9712
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq9712
       grind)
    | exact resolve eq13 eq9712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9772 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq9736
  have eq9799 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9772
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq9772
    | exact resolve eq9772 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9772
  have eq9809 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq498 eq9799
    | (have j1 := eq498 y x
       grind)
    | exact resolve eq9799 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9799
  have eq9810 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9809
       have r₂ := eq9732
       grind)
    | exact resolve eq9809 eq9732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9809
  have eq10062 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq9810
       grind)
    | exact superpose eq9810 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq9810
       grind)
    | exact resolve eq12 eq9810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9810
  have eq10103 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq10062
  have eq10129 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10103
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq10103
    | exact resolve eq10103 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10103
  have eq10147 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9712 eq10129
    | exact resolve eq10129 eq9712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9712 eq10129
  have eq10151 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq498 eq10147
    | (have j1 := eq498 y x
       grind)
    | exact resolve eq10147 eq498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq10147
  have eq10153 : x = (M.op x y) := by
    first
    | (have r₁ := eq10151
       have r₂ := eq9732
       grind)
    | exact resolve eq10151 eq9732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9732 eq10151
  have eq10154 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10153
       grind)
    | exact superpose eq10153 eq16
    | exact resolve eq16 eq10153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10158 : x ≠ x ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq10153
       grind)
    | exact superpose eq10153 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq10153
       grind)
    | exact resolve eq13 eq10153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10194 : x = (k y x) ∨ x = (M.op y x) := by grind
  clear eq10158
  have eq10381 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq499 y x
       have i₂ := eq10194
       grind)
    | exact superpose eq10194 eq499
    | (have j0 := eq499 y x
       grind)
    | exact resolve eq499 eq10194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq499 eq10194
  have eq10394 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq10381
  have eq10400 : x = (M.op y x) := by
    first
    | (have r₁ := eq10394
       have r₂ := eq10154
       grind)
    | exact resolve eq10394 eq10154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10394
  have eq10404 : x ≠ x ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq10400
       grind)
    | exact superpose eq10400 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10400
       grind)
    | exact resolve eq12 eq10400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10400
  have eq10409 : (M.op x y) = (k y x) := by grind
  clear eq10404
  have eq10411 : x = (k y x) := by
    first
    | (have i₁ := eq10409
       have i₂ := eq10153
       grind)
    | exact superpose eq10153 eq10409
    | exact resolve eq10409 eq10153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10153 eq10409
  have eq10425 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq830 y x
       have i₂ := eq10411
       grind)
    | exact superpose eq10411 eq830
    | (have j0 := eq830 y x
       grind)
    | exact resolve eq830 eq10411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq10411
  have eq10428 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10425
  have eq10435 : False := by grind
  exact eq10435

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_y_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq175 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq176 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : x ≠ (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq530 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
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
  have eq531 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 : G, (M.op (M.op X0 x) (M.op (M.op x y) y)) = X0 := by
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
  have eq534 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (M.op (M.op X2 X3) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) (M.op (M.op X2 X3) X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op x (M.op (M.op y X1) X1))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq530 eq16
    | exact resolve eq16 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq548 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 x)) (M.op X0 (M.op (M.op x y) y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq533 eq16
    | exact resolve eq16 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (M.op X0 x) x)) X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq533 eq548
    | exact resolve eq548 eq533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq548
  have eq647 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
  clear eq18
  have eq649 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op (M.op X0 X2) X2)) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq697 : ∀ X0 X1 : G, (k X1 X0) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq732 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq647
       grind)
    | exact superpose eq647 eq40
    | exact resolve eq40 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq735 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq732
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq732
    | exact resolve eq732 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq737 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq735
    | exact resolve eq735 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq747 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq737 eq649
    | exact resolve eq649 eq737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq755 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq747
       have r₂ := eq27
       grind)
    | exact resolve eq747 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq760 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq755 eq176
    | (have r₁ := eq176
       have r₂ := eq755
       grind)
    | exact resolve eq176 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq755
  have eq767 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq760
  have eq770 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq767
       have r₂ := eq178
       grind)
    | exact resolve eq767 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq767
  have eq777 : (τ (σ x)) = (k y (τ (σ x))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq770 eq108
    | exact resolve eq108 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq770
  have eq784 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq777
    | exact resolve eq777 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq787 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq784
       have r₂ := eq177
       grind)
    | exact resolve eq784 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq784
  have eq790 : x = (k y x) := by
    first
    | (have r₁ := eq787
       have r₂ := eq175
       grind)
    | exact resolve eq787 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq787
  have eq794 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq647
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq647
    | exact resolve eq647 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq795 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq790
       grind)
    | exact superpose eq790 eq37
    | exact resolve eq37 eq790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq797 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq794
  have eq800 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq795
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq795
    | exact resolve eq795 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq805 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq800 eq649
    | exact resolve eq649 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649 eq800
  have eq809 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq805
  have eq816 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq797
       grind)
    | exact superpose eq797 eq24
    | exact resolve eq24 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq816
    | exact resolve eq816 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq831 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq809 eq27
    | exact resolve eq27 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq834 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (M.op (σ y) X0) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq809 eq531
    | exact resolve eq531 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq809
  have eq863 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq830 eq831
    | (have r₁ := eq831
       have r₂ := eq830
       grind)
    | exact resolve eq831 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq864 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq863
  have eq867 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq864 eq27
    | exact resolve eq27 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq870 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ y) X0) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq864 eq531
    | exact resolve eq531 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq871 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq864 eq534
    | exact resolve eq534 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq878 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq871
    | (have j0 := eq871 X0
       grind)
    | exact resolve eq871 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq871
  have eq880 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq864 eq878
    | exact resolve eq878 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq878
  have eq881 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq830 eq867
    | exact resolve eq867 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq882 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq881
  have eq925 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq880 eq530
    | exact resolve eq530 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq937 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq797 eq925
    | exact resolve eq925 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797 eq925
  have eq945 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq937 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937
  have eq950 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq945
  have eq957 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq950 eq42
    | exact resolve eq42 eq950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq950
  have eq960 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq957
    | exact resolve eq957 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq962 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq960
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq960
    | exact resolve eq960 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq964 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq830 eq962
    | exact resolve eq962 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq962
  have eq1201 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op X2 x) x))) = (M.op X1 (M.op (M.op (M.op X0 X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq532 X1 (M.op X0 (M.op (M.op X2 x) x)) X2 X3
       have i₂ := eq567 X2 X0
       grind)
    | exact superpose eq567 eq532
    | exact resolve eq532 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq1350 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) x) x)) = (M.op X0 (M.op X1 (M.op (M.op X2 X3) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq535 X1 (M.op X0 (M.op (M.op (M.op X1 X2) x) x)) X2 X3
       have i₂ := eq567 (M.op X1 X2) X0
       grind)
    | exact superpose eq567 eq535
    | exact resolve eq535 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq1430 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X2 x) x))) = (M.op X0 (M.op X1 (M.op (M.op X2 X3) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1350 X0 X1 X2 X3
       have i₂ := eq1201 X1 X0 X2 x
       grind)
    | exact superpose eq1201 eq1350
    | exact resolve eq1350 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201 eq1350
  have eq1497 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ y) (σ y))) (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq834 eq535
    | exact resolve eq535 eq834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq1575 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) X1) X1)) = (M.op X0 (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1497 eq16
    | exact resolve eq16 eq1497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497
  have eq2603 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op x (M.op (M.op y (M.op (σ y) (σ y))) (M.op (M.op (σ x) X1) X1)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1575 eq538
    | exact resolve eq538 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq2624 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) (M.op (M.op y (M.op (σ y) (σ y))) (M.op (M.op (σ x) X1) X1)))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq864 eq2603
    | exact resolve eq2603 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2661 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) (M.op (M.op y (M.op (σ y) (σ y))) (M.op (σ y) (σ y))))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1575 eq2624
    | exact resolve eq2624 eq1575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1575 eq2624
  have eq2671 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) (M.op (M.op y x) x))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2661 X0
       have i₂ := eq1430 (M.op X0 sF0) sF0 y (M.op sF3 sF3)
       grind)
    | exact superpose eq1430 eq2661
    | exact resolve eq2661 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430 eq2661
  have eq2680 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq530 eq2671
    | exact resolve eq2671 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq2684 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq864 eq2680
    | exact resolve eq2680 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2680
  have eq2694 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f2694_14 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f2694_22 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
      intro X0 X1 X2
      grind
    have f2694_23 : X1 ≠ (M.op (M.op X1 X0) X0) := by grind
    have f2694_24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f2694_26 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 := by
      intro X0
      first
      | (have j0 := f2694_14 X0
         grind)
      | (have r₁ := f2694_14 X0
         have r₂ := f2694_24
         grind)
      | exact resolve f2694_14 f2694_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2694_45 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f2694_22 X1 X0 (M.op x y)
         have i₂ := f2694_26 X0
         grind)
      | exact superpose f2694_26 f2694_22
      | exact resolve f2694_22 f2694_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2694_56 : X1 ≠ X1 := by
      first
      | (have i₁ := f2694_23
         have i₂ := f2694_45 X0 X1
         grind)
      | exact superpose f2694_45 f2694_23
      | (have r₁ := f2694_23
         have r₂ := f2694_45 X0 X1
         grind)
      | exact resolve f2694_23 f2694_45
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2694_57 : False := by grind
    exact f2694_57
  have eq2707 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2684 eq834
    | exact resolve eq834 eq2684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq2684
  have eq2720 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2707
  have eq2745 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2720 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq2720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2720
  have eq2754 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2745
  have eq2765 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2754
       have r₂ := eq838
       grind)
    | exact resolve eq2754 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2754
  have eq2811 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2765 eq116
    | exact resolve eq116 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq2817 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq2811
    | exact resolve eq2811 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2811
  have eq2820 : (M.op x y) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq864 eq2817
    | exact resolve eq2817 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2817
  have eq2848 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq697 y y
       have i₂ := eq2820
       grind)
    | exact superpose eq2820 eq697
    | (have j0 := eq697 y y
       grind)
    | exact resolve eq697 eq2820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq2870 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2848
  have eq3013 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq2694 X1 X0
       grind)
    | exact superpose eq2694 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq2694 X1 X1
       grind)
    | exact resolve eq13 eq2694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2694
  have eq5015 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3013 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3013
  have eq5036 : (σ (M.op y y)) = (k (σ y) (σ (M.op y y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 (M.op y y)
       have i₂ := eq5015 y
       grind)
    | exact superpose eq5015 eq37
    | exact resolve eq37 eq5015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq5015
  have eq7562 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq652 y y X0
       have i₂ := eq2820
       grind)
    | exact superpose eq2820 eq652
    | (have j0 := eq652 y y x
       grind)
    | exact resolve eq652 eq2820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2820
  have eq7588 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq964 eq652
    | (have j0 := eq652 (σ y) (σ y) x
       grind)
    | exact resolve eq652 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq7726 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7588 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7588
  have eq7732 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq7562 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7562
  have eq7814 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq870 eq7726
    | exact resolve eq7726 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq870 eq7726
  have eq7821 : x = y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq530 eq7732
    | exact resolve eq7732 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq7732
  have eq7844 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7814
       have r₂ := eq882
       grind)
    | exact resolve eq7814 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7814
  have eq7849 : y = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq864 eq7821
    | exact resolve eq7821 eq864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq864 eq7821
  have eq7865 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq7849
       have r₂ := eq2870
       grind)
    | exact resolve eq7849 eq2870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2870 eq7849
  have eq8285 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7844 eq28
    | (have j0 := eq28 (σ y) (σ y)
       grind)
    | (have r₁ := eq28 (σ y) (σ y)
       have r₂ := eq7844
       grind)
    | (have r₁ := eq28 y x
       have r₂ := eq7844
       grind)
    | exact resolve eq28 eq7844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq7844
  have eq8301 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8285
  have eq8318 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq964 eq8301
    | exact resolve eq8301 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964 eq8301
  have eq8339 : x = (M.op x y) := by
    first
    | (have r₁ := eq8318
       have r₂ := eq882
       grind)
    | exact resolve eq8318 eq882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882 eq8318
  have eq8353 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq8339
       grind)
    | exact superpose eq8339 eq22
    | exact resolve eq22 eq8339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq8339
  have eq8373 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq8353 eq20
    | exact resolve eq20 eq8353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8353
  have eq9386 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5036
       have i₂ := eq7865
       grind)
    | exact superpose eq7865 eq5036
    | exact resolve eq5036 eq7865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5036 eq7865
  have eq9419 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9386
  have eq9438 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9419
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9419
    | exact resolve eq9419 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9419
  have eq9448 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2765 eq9438
    | exact resolve eq9438 eq2765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2765 eq9438
  have eq9451 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq9448
       have r₂ := eq838
       grind)
    | exact resolve eq9448 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq9448
  have eq9454 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq9451 eq27
    | exact resolve eq27 eq9451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9451
  have eq9468 : False := by grind
  exact eq9468

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyx_pyx_pxy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq44 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq44 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq44 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ X0) (σ X1)
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq45 (τ X0)
       grind)
    | exact superpose eq45 eq18
    | exact resolve eq18 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq85 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq85
    | exact resolve eq85 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq85
  have eq97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq180 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq198 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq9
    | exact resolve eq9 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq97 y
       grind)
    | exact superpose eq97 eq180
    | exact resolve eq180 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq722 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq674
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq674
    | (have j1 := eq58 y x
       grind)
    | exact resolve eq674 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq674
  have eq723 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq722
  have eq4545 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y y)) (M.op (M.op (σ y) X0) X0)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq723
       grind)
    | exact superpose eq723 eq9
    | exact resolve eq9 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq4573 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4545 x
       have i₂ := eq198 y x
       grind)
    | exact superpose eq198 eq4545
    | exact resolve eq4545 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq4545
  have eq4709 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4573
       grind)
    | exact superpose eq4573 eq10
    | exact resolve eq10 eq4573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4573
  have eq4757 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq4709
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4709
    | exact resolve eq4709 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4709
  have eq4949 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4757
       grind)
    | exact superpose eq4757 eq16
    | exact resolve eq16 eq4757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4757
  have eq4950 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq4949
       have r₂ := eq97 x
       grind)
    | exact resolve eq4949 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4949
  have eq4963 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq4950
       grind)
    | exact superpose eq4950 eq9
    | exact resolve eq9 eq4950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4950
  have eq4998 : x = y := by
    first
    | (have i₁ := eq4963 x
       have i₂ := eq9 x y x
       grind)
    | exact superpose eq9 eq4963
    | exact resolve eq4963 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4963
  have eq5002 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4998
       grind)
    | exact superpose eq4998 eq16
    | exact resolve eq16 eq4998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4998
  have eq5004 : False := by grind
  exact eq5004

/-- `Equation1663`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pxy_pyy_pyx_Equation1663 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1663 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1663.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X3)) = X0 := by
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
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
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
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
  have eq175 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X5)) = X1 := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq16 X1 (M.op X0 X2) (M.op (M.op X2 x) x) X5
       have i₂ := eq16 X0 X2 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 x (M.op (M.op x x) x)
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : y ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq182 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : x = (M.op (M.op x y) y) := by
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
  have eq185 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ y) (σ x)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : x ≠ y ∨ (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq184 eq13
    | (have j0 := eq13 y (M.op x y)
       grind)
    | exact resolve eq13 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op x X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq178 eq180
    | exact resolve eq180 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq376 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq193 eq180
    | exact resolve eq180 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq388 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq198 eq180
    | exact resolve eq180 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq716 : (M.op x y) = (k y x) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq719 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq11 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq11 (M.op X1 (M.op X1 X1)) X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq724 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op (k X0 X1) X3)) = X2 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X1 X0 X3
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq760 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq723 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq723 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq723 (M.op X1 (M.op X1 X1)) X1
       have r₂ := eq13 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq723 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq723 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq796 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq716
       grind)
    | exact superpose eq716 eq39
    | exact resolve eq39 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1113 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1112
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1112
    | exact resolve eq1112 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1113
    | exact resolve eq1113 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1113
  have eq1123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1115 eq719
    | exact resolve eq719 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1130 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1123
       have r₂ := eq27
       grind)
    | exact resolve eq1123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq2745 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1130 eq796
    | exact resolve eq796 eq1130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1130
  have eq2759 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2745
    | exact resolve eq2745 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2745
  have eq2760 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq2759
  have eq2788 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2760 eq141
    | exact resolve eq141 eq2760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq2797 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq2788
    | exact resolve eq2788 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2788
  have eq2800 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq716 eq2797
    | exact resolve eq2797 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716 eq2797
  have eq2801 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2800
  have eq2809 : y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq796 x
       have i₂ := eq2801
       grind)
    | exact superpose eq2801 eq796
    | exact resolve eq796 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2818 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq180 x x
       have i₂ := eq2801
       grind)
    | exact superpose eq2801 eq180
    | exact resolve eq180 eq2801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2801
  have eq2831 : y = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2809
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2809
    | exact resolve eq2809 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2809
  have eq2832 : y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2831
  have eq2838 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2818
       grind)
    | exact superpose eq2818 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2818
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2818
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2818
       grind)
    | exact resolve eq13 eq2818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2818
  have eq2848 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2838
  have eq2854 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2848
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2848
    | exact resolve eq2848 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2848
  have eq3021 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq2832
       grind)
    | exact superpose eq2832 eq39
    | exact resolve eq39 eq2832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq2832
  have eq3029 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3021
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3021
    | exact resolve eq3021 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3021
  have eq3035 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2854
       grind)
    | exact superpose eq2854 eq40
    | exact resolve eq40 eq2854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2854
  have eq3041 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3035
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3035
    | exact resolve eq3035 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq3043 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq3041
    | exact resolve eq3041 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041
  have eq3086 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3029 eq719
    | exact resolve eq719 eq3029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3029
  have eq3095 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3086
  have eq3171 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3095 eq180
    | exact resolve eq180 eq3095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095
  have eq3213 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3171 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq3171
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3171
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq3171
       grind)
    | exact resolve eq13 eq3171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3171
  have eq3224 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3213
  have eq3239 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq3224
    | exact resolve eq3224 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3224
  have eq3243 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3043 eq3239
    | exact resolve eq3239 eq3043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3043 eq3239
  have eq3244 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3243
       have r₂ := eq27
       grind)
    | exact resolve eq3243 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3243
  have eq3248 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3244 eq182
    | (have r₁ := eq182
       have r₂ := eq3244
       grind)
    | exact resolve eq182 eq3244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq3249 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3244 eq185
    | exact resolve eq185 eq3244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3251 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3244 eq234
    | exact resolve eq234 eq3244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq3252 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3248
  have eq3268 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3249 eq796
    | exact resolve eq796 eq3249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3270 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3249 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3271 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3249 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq3249
       grind)
    | exact resolve eq13 eq3249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3249
  have eq3282 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq3270
  have eq3300 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3282
       have r₂ := eq3271
       grind)
    | exact resolve eq3282 eq3271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271 eq3282
  have eq3307 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3300 eq115
    | exact resolve eq115 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq3321 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq3307
    | exact resolve eq3307 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3307
  have eq3328 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op x X1)) = X0 ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq724 y y X0 X1
       have i₂ := eq3321
       grind)
    | exact superpose eq3321 eq724
    | (have j0 := eq724 y y x x
       grind)
    | exact resolve eq724 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3332 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op x X1)) = X0 ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq3328 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328
  have eq3333 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = X0 ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3332 X0 x
       have i₂ := eq376 (M.op X0 y) x
       grind)
    | (have i₁ := eq3332 X0 y
       have i₂ := eq376 (M.op X0 y) x
       grind)
    | exact superpose eq376 eq3332
    | (have j0 := eq3332 X0 y
       grind)
    | exact resolve eq3332 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332
  have eq3360 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ y) X1)) (k (σ y) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3252 eq179
    | exact resolve eq179 eq3252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq3381 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (k (σ y) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3251 eq3360
    | exact resolve eq3360 eq3251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3251 eq3360
  have eq3831 : (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3252 eq3381
    | exact resolve eq3381 eq3252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381
  have eq3869 : (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq3831
  have eq4165 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3869 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq3869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4166 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3869 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq3869
       grind)
    | exact resolve eq13 eq3869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3869
  have eq4178 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq4165
  have eq4191 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4178
       have r₂ := eq4166
       grind)
    | exact resolve eq4178 eq4166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4166 eq4178
  have eq4329 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1115 eq4191
    | exact resolve eq4191 eq1115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115 eq4191
  have eq4338 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq4329
  have eq4648 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3268 eq152
    | exact resolve eq152 eq3268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq3268
  have eq4660 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq4648
    | exact resolve eq4648 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4648
  have eq4714 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4660 eq3252
    | exact resolve eq3252 eq4660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3252
  have eq4730 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4660 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4660
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4660
       grind)
    | exact resolve eq13 eq4660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4660
  have eq4742 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by grind
  clear eq4730
  have eq4756 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq4714
  have eq4764 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq4742
    | exact resolve eq4742 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4742
  have eq4770 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3244 eq4764
    | exact resolve eq4764 eq3244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3244 eq4764
  have eq4915 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4756 eq107
    | exact resolve eq107 eq4756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq4756
  have eq4937 : x = (k y x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq4915
    | exact resolve eq4915 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915
  have eq4952 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4770 eq90
    | exact resolve eq90 eq4770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4770
  have eq4964 : y = (k x y) ∨ x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq4952
    | exact resolve eq4952 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4952
  have eq4969 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq4338 eq133
    | exact resolve eq133 eq4338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq4338
  have eq4984 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq4969
    | exact resolve eq4969 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq4969
  have eq5034 : x ≠ y ∨ x = (k x y) ∨ y = (M.op x y) := by grind
  have eq7876 : y = (M.op y y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3333 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3333
    | (have j0 := eq3333 x
       grind)
    | exact resolve eq3333 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3333
  have eq7931 : y ≠ y ∨ y = (k y y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq7876
       grind)
    | exact superpose eq7876 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq7876
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq7876
       grind)
    | exact resolve eq13 eq7876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7876
  have eq7948 : y = (k y y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq7931
  have eq7961 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq3321 eq7948
    | exact resolve eq7948 eq3321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321 eq7948
  have eq7970 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq7961 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq7961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7971 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq7961 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq7961
       grind)
    | exact resolve eq13 eq7961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7961
  have eq7988 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq7970
  have eq7995 : x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq7988
       have r₂ := eq7971
       grind)
    | exact resolve eq7988 eq7971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7971 eq7988
  have eq8029 : x = y ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq7995 eq4984
    | exact resolve eq4984 eq7995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4984
  have eq8039 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq8029
  have eq8050 : y = (k y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq796 x
       have i₂ := eq8039
       grind)
    | exact superpose eq8039 eq796
    | exact resolve eq796 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8052 : y = (k x x) ∨ x = y ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq8039
       grind)
    | exact superpose eq8039 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8059 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq180 x x
       have i₂ := eq8039
       grind)
    | exact superpose eq8039 eq180
    | exact resolve eq180 eq8039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8039
  have eq8070 : y = (k x x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq8052
  have eq8080 : y = (M.op x y) ∨ y = (k y x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8050
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8050
    | exact resolve eq8050 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8050
  have eq8081 : y = (k y x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq8080
  have eq8110 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq8059
       grind)
    | exact superpose eq8059 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq8059
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq8059
       grind)
    | exact resolve eq13 eq8059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8059
  have eq8127 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq8110
  have eq8143 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8127
    | exact resolve eq8127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8127
  have eq8169 : x = y ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4937
       have i₂ := eq8081
       grind)
    | exact superpose eq8081 eq4937
    | exact resolve eq4937 eq8081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4937 eq8081
  have eq8179 : x = y ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq8169
  have eq8184 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq8179
       have r₂ := eq5034
       grind)
    | exact resolve eq8179 eq5034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5034 eq8179
  have eq8193 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq8184
       grind)
    | exact superpose eq8184 eq40
    | exact resolve eq40 eq8184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8195 : x ≠ x ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq783 x y
       have i₂ := eq8184
       grind)
    | exact superpose eq8184 eq783
    | (have j0 := eq783 x y
       grind)
    | (have r₁ := eq783 x y
       have r₂ := eq8184
       grind)
    | exact resolve eq783 eq8184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8184
  have eq8198 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq8195
  have eq8205 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8198
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8198
    | exact resolve eq8198 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8198
  have eq8207 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8193
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8193
    | exact resolve eq8193 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8193
  have eq8239 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4964
       have i₂ := eq8143
       grind)
    | exact superpose eq8143 eq4964
    | exact resolve eq4964 eq8143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4964
  have eq8242 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq8143
       grind)
    | exact superpose eq8143 eq40
    | exact resolve eq40 eq8143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq8143
  have eq8247 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8239
  have eq8254 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq8242
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8242
    | exact resolve eq8242 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8242
  have eq8258 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq8254
    | exact resolve eq8254 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8254
  have eq8262 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8207 eq8258
    | exact resolve eq8258 eq8207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8258
  have eq8285 : (k (M.op x y) x) = (τ (k (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8262 eq131
    | exact resolve eq131 eq8262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq8262
  have eq8318 : (k x x) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq97 eq8285
    | exact resolve eq8285 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq8285
  have eq8327 : y = (k (M.op x y) x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8070 eq8318
    | exact resolve eq8318 eq8070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8070 eq8318
  have eq8332 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8247 eq8327
    | exact resolve eq8327 eq8247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8247 eq8327
  have eq8334 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq7995 eq8332
    | exact resolve eq8332 eq7995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7995 eq8332
  have eq8335 : y = (M.op x y) ∨ x = y := by grind
  clear eq8334
  have eq8339 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq8335
       grind)
    | exact superpose eq8335 eq24
    | exact resolve eq24 eq8335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8344 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq184
       have i₂ := eq8335
       grind)
    | exact superpose eq8335 eq184
    | exact resolve eq184 eq8335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq8346 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq8335
  have eq8351 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq8339
    | exact resolve eq8339 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8339
  have eq8425 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq8344 eq796
    | exact resolve eq796 eq8344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8427 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8344 eq11
    | exact resolve eq11 eq8344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8344
  have eq8445 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq8427
  have eq8451 : x = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq8445
       have r₂ := eq8346
       grind)
    | exact resolve eq8445 eq8346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8445
  have eq8456 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq8451 eq41
    | exact resolve eq41 eq8451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8451
  have eq8466 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq8456
    | exact resolve eq8456 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8456
  have eq8468 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq8466
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq8466
    | exact resolve eq8466 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8466
  have eq8470 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq8351 eq8468
    | exact resolve eq8468 eq8351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8468
  have eq8472 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3300 eq8470
    | exact resolve eq8470 eq3300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3300 eq8470
  have eq8479 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) X1)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8472 eq724
    | (have j0 := eq724 (σ y) (σ y) x x
       grind)
    | exact resolve eq724 eq8472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq724
  have eq8481 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8472 eq760
    | (have j0 := eq760 (σ y) (σ y)
       grind)
    | exact resolve eq760 eq8472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8482 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq8481
  have eq8483 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) X1)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq8479 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8479
  have eq8484 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq388 eq8483
    | (have j0 := eq8483 X0 (σ y)
       grind)
    | exact resolve eq8483 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8483
  have eq8789 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq180 y y
       have i₂ := eq8205
       grind)
    | exact superpose eq8205 eq180
    | exact resolve eq180 eq8205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8205
  have eq8819 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8789
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq8789
    | exact resolve eq8789 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8789
  have eq8820 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8819
  have eq8840 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq8820
       grind)
    | exact superpose eq8820 eq18
    | exact resolve eq18 eq8820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8841 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8820
       grind)
    | exact superpose eq8820 eq24
    | exact resolve eq24 eq8820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8845 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq181
       have i₂ := eq8820
       grind)
    | exact superpose eq8820 eq181
    | (have r₁ := eq181
       have r₂ := eq8820
       grind)
    | exact resolve eq181 eq8820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq8820
  have eq8850 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq8845
  have eq8854 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq8841
    | exact resolve eq8841 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8841
  have eq8978 : ∀ X0 : G, (M.op (M.op X0 x) (k (M.op x y) x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8850 eq177
    | exact resolve eq177 eq8850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq9604 : (M.op x y) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8850 eq8978
    | exact resolve eq8978 eq8850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8978
  have eq9641 : (M.op x y) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by grind
  clear eq9604
  have eq9750 : (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9641 eq11
    | exact resolve eq11 eq9641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9751 : (M.op x y) ≠ (k (M.op x y) x) ∨ (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9641 eq13
    | exact resolve eq13 eq9641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9641
  have eq9768 : (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq9750
  have eq9782 : (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9768
       have r₂ := eq9751
       grind)
    | exact resolve eq9768 eq9751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9751 eq9768
  have eq11059 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq8425 eq41
    | exact resolve eq41 eq8425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq8425
  have eq11067 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have i₁ := eq11059
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11059
    | exact resolve eq11059 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11059
  have eq11069 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq8351 eq11067
    | exact resolve eq11067 eq8351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8351 eq11067
  have eq11071 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8207 eq11069
    | exact resolve eq11069 eq8207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8207 eq11069
  have eq11145 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11071 eq783
    | (have j0 := eq783 (σ x) (σ y)
       grind)
    | (have r₁ := eq783 (σ x) (σ y)
       have r₂ := eq11071
       grind)
    | exact resolve eq783 eq11071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq11071
  have eq11148 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq11145
  have eq11150 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11148
    | exact resolve eq11148 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11148
  have eq11155 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8850 eq11150
    | exact resolve eq11150 eq8850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8850 eq11150
  have eq14538 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq8484
    | (have j0 := eq8484 (σ x)
       grind)
    | exact resolve eq8484 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14540 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq185 eq8484
    | exact resolve eq8484 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq8484
  have eq14583 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14538 eq175
    | exact resolve eq175 eq14538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq14610 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14538 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq14538
       grind)
    | exact resolve eq13 eq14538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14538
  have eq14627 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq14610
  have eq14636 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8472 eq14627
    | exact resolve eq14627 eq8472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8472 eq14627
  have eq15243 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14583 eq180
    | exact resolve eq180 eq14583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14583
  have eq15262 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) X0)) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14636 eq15243
    | exact resolve eq15243 eq14636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14636 eq15243
  have eq15274 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq388 eq15262
    | (have j0 := eq15262 (σ y)
       grind)
    | exact resolve eq15262 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388 eq15262
  have eq15310 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15274 eq180
    | exact resolve eq180 eq15274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15274
  have eq15321 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq15310
  have eq15338 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15321 eq796
    | exact resolve eq796 eq15321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15347 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15321 eq180
    | exact resolve eq180 eq15321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15321
  have eq15381 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15347 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (σ x)
       grind)
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (σ x)
       have r₂ := eq15347
       grind)
    | exact resolve eq13 eq15347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15398 : (M.op (M.op (σ x) (σ y)) (σ x)) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15381
  have eq15422 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (k (M.op (σ x) (σ y)) (σ x))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15398 eq178
    | exact resolve eq178 eq15398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq15431 : (σ x) ≠ (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15398 eq13
    | (have j0 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq15398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15455 : (σ x) ≠ (k (M.op (σ x) (σ y)) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15347 eq15431
    | exact resolve eq15431 eq15347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15347 eq15431
  have eq15644 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ x)) (k (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15398 eq15422
    | exact resolve eq15422 eq15398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15422
  have eq15683 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ x)) (k (M.op (σ x) (σ y)) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq15644
  have eq15904 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15338 eq90
    | exact resolve eq90 eq15338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15338
  have eq15912 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq15904
    | exact resolve eq15904 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15904
  have eq15913 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15398 eq15912
    | exact resolve eq15912 eq15398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15398 eq15912
  have eq15917 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15913 eq38
    | exact resolve eq38 eq15913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq15913
  have eq15923 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15917
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15917
    | exact resolve eq15917 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15917
  have eq15952 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15923 eq15455
    | (have r₁ := eq15455
       have r₂ := eq15923
       grind)
    | exact resolve eq15455 eq15923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15455
  have eq15953 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15923 eq15683
    | exact resolve eq15683 eq15923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15683 eq15923
  have eq15962 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq15953
  have eq15963 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq15952
  have eq15964 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq15963
  have eq15976 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq15964
  have eq18631 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11155 eq180
    | exact resolve eq180 eq11155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq11155
  have eq18650 : x = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18631
    | exact resolve eq18631 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18631
  have eq18676 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18650 eq9782
    | exact resolve eq9782 eq18650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9782
  have eq18692 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18650 eq37
    | exact resolve eq37 eq18650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18650
  have eq18705 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq18676
  have eq18716 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18692
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18692
    | exact resolve eq18692 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18692
  have eq18737 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8854 eq18716
    | exact resolve eq18716 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18716
  have eq18950 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18737 eq719
    | exact resolve eq719 eq18737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq18986 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18950
  have eq19229 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18986 eq796
    | exact resolve eq796 eq18986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq18986
  have eq19265 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19229
    | exact resolve eq19229 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19229
  have eq19266 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19265
  have eq19269 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18737 eq19266
    | exact resolve eq19266 eq18737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18737 eq19266
  have eq19270 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19269 eq27
    | exact resolve eq27 eq19269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19279 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19269 eq14540
    | exact resolve eq14540 eq19269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14540
  have eq19371 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19279
  have eq19379 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq19371
       have r₂ := eq8482
       grind)
    | exact resolve eq19371 eq8482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8482 eq19371
  have eq19384 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19270
       have r₂ := eq8854
       grind)
    | exact resolve eq19270 eq8854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8854 eq19270
  have eq19388 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq19379
    | exact resolve eq19379 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19379
  have eq19391 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19269 eq19388
    | exact resolve eq19388 eq19269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19269 eq19388
  have eq19392 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19384 eq19391
    | exact resolve eq19391 eq19384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19391
  have eq19393 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19392
  have eq19660 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19393 eq15962
    | exact resolve eq15962 eq19393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15962
  have eq19678 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19393 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq19393
       grind)
    | exact resolve eq13 eq19393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19393
  have eq19695 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19678
  have eq19698 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq19660
  have eq19718 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19698
       have r₂ := eq15976
       grind)
    | exact resolve eq19698 eq15976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15976 eq19698
  have eq19727 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19718 eq90
    | exact resolve eq90 eq19718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq19718
  have eq19736 : x = (k x (τ (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq19727
    | exact resolve eq19727 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19727
  have eq19855 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19695 eq141
    | exact resolve eq141 eq19695
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq19695
  have eq19871 : x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq19855
    | exact resolve eq19855 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19855
  have eq19888 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18705
       have i₂ := eq19871
       grind)
    | exact superpose eq19871 eq18705
    | exact resolve eq18705 eq19871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18705 eq19871
  have eq19902 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq19888
  have eq19910 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19384 eq19902
    | exact resolve eq19902 eq19384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19384 eq19902
  have eq19911 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19910
  have eq20024 : x = (k x (τ (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19911 eq19736
    | exact resolve eq19736 eq19911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19736 eq19911
  have eq20025 : x = (k x (τ (σ x))) ∨ x = (M.op x y) := by grind
  clear eq20024
  have eq20084 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq20025
    | exact resolve eq20025 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq20025
  have eq20291 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq760 x x
       have i₂ := eq20084
       grind)
    | exact superpose eq20084 eq760
    | (have j0 := eq760 x x
       grind)
    | (have r₁ := eq760 x x
       have r₂ := eq20084
       grind)
    | exact resolve eq760 eq20084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760 eq20084
  have eq20292 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq20291
  have eq20293 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq20292
  have eq20329 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq376 X0 x
       have i₂ := eq20293
       grind)
    | exact superpose eq20293 eq376
    | exact resolve eq376 eq20293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376
  have eq20486 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20293
       have i₂ := eq20329 x
       grind)
    | exact superpose eq20329 eq20293
    | exact resolve eq20293 eq20329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20293 eq20329
  have eq20541 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq20486
  have eq20567 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8840 eq20541
    | exact resolve eq20541 eq8840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8840 eq20541
  have eq20568 : x = (M.op x y) := by grind
  clear eq20567
  have eq20604 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq20568
       grind)
    | exact superpose eq20568 eq18
    | exact resolve eq18 eq20568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq20605 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq20568
       grind)
    | exact superpose eq20568 eq22
    | exact resolve eq22 eq20568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq20648 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8346
       have i₂ := eq20568
       grind)
    | exact superpose eq20568 eq8346
    | (have r₁ := eq8346
       have r₂ := eq20568
       grind)
    | exact resolve eq8346 eq20568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8346
  have eq20669 : y = (M.op x y) := by grind
  clear eq20648
  have eq20706 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq20604
       have i₂ := eq20669
       grind)
    | exact superpose eq20669 eq20604
    | exact resolve eq20604 eq20669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20604
  have eq20710 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq20669
       grind)
    | exact superpose eq20669 eq24
    | exact resolve eq24 eq20669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq20716 : x ≠ (M.op x y) ∨ (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq192
       have i₂ := eq20669
       grind)
    | exact superpose eq20669 eq192
    | exact resolve eq192 eq20669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq20669
  have eq20721 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq20716
       have r₂ := eq20568
       grind)
    | exact resolve eq20716 eq20568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20568 eq20716
  have eq20727 : (σ x) = (σ y) := by
    first
    | exact superpose eq20605 eq20710
    | exact resolve eq20710 eq20605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20710
  have eq20729 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20706 eq20721
    | exact resolve eq20721 eq20706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20706 eq20721
  have eq20732 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20727 eq26
    | exact resolve eq26 eq20727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq20727
  have eq20891 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20605 eq20
    | exact resolve eq20 eq20605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20605
  have eq21637 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20729 eq37
    | exact resolve eq37 eq20729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq20729
  have eq21655 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq21637
    | exact resolve eq21637 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq21637
  have eq21657 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq20891 eq21655
    | exact resolve eq21655 eq20891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21655
  have eq21687 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20732 eq11
    | exact resolve eq11 eq20732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20732
  have eq21705 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21687
  have eq21720 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21657 eq21705
    | exact resolve eq21705 eq21657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21657 eq21705
  have eq21721 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21720
  have eq21728 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq21721 eq27
    | exact resolve eq27 eq21721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq21721
  have eq21843 : False := by grind
  exact eq21843

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_x_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X2 X0) X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 y) y)) := by
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
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X0) X2) ≠ X0 ∨ (k X2 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X1 X0) X0)
       have i₂ := eq14 X0 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X2 (M.op (M.op X1 X0) X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : x ≠ (M.op x y) ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
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
  have eq81 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq113 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq89
    | (have j0 := eq89 (σ x) (σ X0)
       grind)
    | exact resolve eq89 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq120 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq89 x y
       grind)
    | exact superpose eq89 eq44
    | (have j1 := eq89 x y
       grind)
    | exact resolve eq44 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq120
    | exact resolve eq120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq131 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq128
    | exact resolve eq128 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq131
    | exact resolve eq131 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq151 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq172 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq151 eq16
    | exact resolve eq16 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq132 eq89
    | (have j0 := eq89 (σ x) (σ y)
       grind)
    | exact resolve eq89 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq200 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq199
    | exact resolve eq199 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq203 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq200
       have r₂ := eq27
       grind)
    | exact resolve eq200 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq203
    | exact resolve eq203 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq207 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq27
    | exact resolve eq27 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq268 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (M.op X0 (σ y)) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq205 eq51
    | exact resolve eq51 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq275 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq268
    | (have j0 := eq268 (σ x)
       grind)
    | exact resolve eq268 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq288 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq275
    | exact resolve eq275 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq293 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq288
  have eq294 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq293
    | exact resolve eq293 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq295 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq294
    | exact resolve eq294 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq300 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq295
  have eq310 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq205 eq54
    | exact resolve eq54 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq317 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq310
    | (have j0 := eq310 X0
       grind)
    | exact resolve eq310 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq327 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq205 eq317
    | exact resolve eq317 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq331 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq371 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq331 eq14
    | exact resolve eq14 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X1 : G, (σ x) = (M.op (σ y) (M.op (M.op X1 (σ x)) (σ x))) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq331 eq14
    | exact resolve eq14 eq331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq205 eq81
    | (have r₁ := eq81
       have r₂ := eq205
       grind)
    | exact resolve eq81 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq205
  have eq472 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq471
  have eq585 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq472 eq331
    | exact resolve eq331 eq472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq598 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq585
  have eq701 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op X2 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X1 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 (M.op (M.op X2 X0) X0)
       have i₂ := eq14 X0 (M.op X1 X0) X2
       grind)
    | exact superpose eq14 eq68
    | (have j0 := eq68 X0 X1 (M.op (M.op X2 X0) X0)
       grind)
    | (have r₁ := eq68 X0 X1 (M.op (M.op X2 X0) X0)
       have r₂ := eq14 X0 (M.op X1 X0) X2
       grind)
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq719 : ∀ X0 X1 X2 : G, (k (M.op (M.op X2 X0) X0) (M.op (M.op X1 X0) X0)) = (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X1 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq701 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq727 : ∀ X0 X1 X2 : G, (k (M.op (M.op X2 X0) X0) (M.op (M.op X1 X0) X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq719 X0 X1 X2
       have i₂ := eq14 X0 (M.op X2 X0) X1
       grind)
    | exact superpose eq14 eq719
    | exact resolve eq719 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq893 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq598 eq372
    | exact resolve eq372 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq598
  have eq912 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq893
  have eq918 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq912 eq132
    | exact resolve eq132 eq912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq922 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq918
  have eq927 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq922
       have r₂ := eq207
       grind)
    | exact resolve eq922 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq931 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq927 eq472
    | exact resolve eq472 eq927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq472 eq927
  have eq955 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq931
  have eq1256 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq955 eq132
    | exact resolve eq132 eq955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq955
  have eq1260 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1256
  have eq1265 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1260
       have r₂ := eq207
       grind)
    | exact resolve eq1260 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq1260
  have eq1305 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1265 eq371
    | exact resolve eq371 eq1265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371 eq1265
  have eq1315 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1305
  have eq1326 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1315 eq300
    | exact resolve eq300 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1345 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1326
  have eq1392 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1345 eq26
    | exact resolve eq26 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1401 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1345 eq132
    | exact resolve eq132 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq1345
  have eq1460 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1401
  have eq1465 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1460
       have i₂ := eq69 sF2
       grind)
    | exact superpose eq69 eq1460
    | exact resolve eq1460 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1460
  have eq1574 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1392 eq300
    | exact resolve eq300 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392
  have eq1592 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1574
  have eq1610 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1592 eq27
    | exact resolve eq27 eq1592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq1677 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1465 eq300
    | exact resolve eq300 eq1465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300 eq1465
  have eq1695 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq1677
  have eq1703 : x = (M.op x y) := by
    first
    | (have r₁ := eq1695
       have r₂ := eq1610
       grind)
    | exact resolve eq1695 eq1610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1610 eq1695
  have eq1709 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1703 eq20
    | exact resolve eq20 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1712 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1703 eq53
    | exact resolve eq53 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1713 : x ≠ x ∨ (M.op y x) = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq1703 eq80
    | (have r₁ := eq80
       have r₂ := eq1703
       grind)
    | exact resolve eq80 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1718 : y = (M.op x (M.op x y)) := by
    first
    | exact superpose eq1703 eq258
    | exact resolve eq258 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1720 : (M.op y x) = (M.op y y) ∨ x = (k x y) := by grind
  clear eq1713
  have eq1722 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1718
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1718
    | exact resolve eq1718 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1718
  have eq1727 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq1712 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1712
    | (have j0 := eq1712 X0
       grind)
    | exact resolve eq1712 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712
  have eq1729 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1709
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1709
    | exact resolve eq1709 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709
  have eq1731 : y = (M.op x x) := by
    first
    | exact superpose eq1703 eq1722
    | exact resolve eq1722 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722
  have eq1733 : ∀ X0 : G, y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | exact superpose eq1703 eq1727
    | exact resolve eq1727 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq1747 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1729 eq26
    | exact resolve eq26 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1808 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq14
    | exact resolve eq14 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1897 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op y (M.op (M.op x y) y)) (M.op (M.op X0 (M.op (M.op x y) y)) (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq258 eq727
    | exact resolve eq727 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258 eq727
  have eq1988 : ∀ X0 : G, (M.op x y) = (k (M.op y (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1703 eq1897
    | exact resolve eq1897 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq1993 : ∀ X0 : G, (M.op x y) = (k (M.op y (M.op x y)) (M.op (M.op X0 (M.op x y)) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq1988 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1988
    | (have j0 := eq1988 X0
       grind)
    | exact resolve eq1988 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1988
  have eq1998 : ∀ X0 : G, x = (k (M.op y x) (M.op (M.op X0 x) x)) := by
    intro X0
    first
    | exact superpose eq1703 eq1993
    | exact resolve eq1993 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1993
  have eq2837 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1729 eq113
    | (have j0 := eq113 X0
       grind)
    | exact resolve eq113 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq2838 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq1729 eq2837
    | (have j0 := eq2837 X0
       grind)
    | exact resolve eq2837 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2837
  have eq2863 : (σ (k x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2838 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2838
    | (have j0 := eq2838 y
       grind)
    | exact resolve eq2838 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2838
  have eq2881 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1747 eq2863
    | exact resolve eq2863 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq2898 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2881
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq2881
    | exact resolve eq2881 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq2881
  have eq2911 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1729 eq2898
    | exact resolve eq2898 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2898
  have eq2921 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1747 eq2911
    | exact resolve eq2911 eq1747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747 eq2911
  have eq2928 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq2921
       have r₂ := eq27
       grind)
    | exact resolve eq2921 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2921
  have eq2972 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) y) := by
    first
    | exact superpose eq2928 eq172
    | exact resolve eq172 eq2928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq2928
  have eq2974 : (k x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1703 eq2972
    | exact resolve eq2972 eq1703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703 eq2972
  have eq4111 : (M.op y x) = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1720
       have i₂ := eq2974
       grind)
    | exact superpose eq2974 eq1720
    | exact resolve eq1720 eq2974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720
  have eq4123 : y = (M.op (M.op y x) x) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1733 y
       have i₂ := eq4111
       grind)
    | exact superpose eq4111 eq1733
    | exact resolve eq1733 eq4111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1733
  have eq4149 : x = (M.op y y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1808 y
       have i₂ := eq4123
       grind)
    | exact superpose eq4123 eq1808
    | exact resolve eq1808 eq4123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1808 eq4123
  have eq4313 : x = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4111
       have i₂ := eq4149
       grind)
    | exact superpose eq4149 eq4111
    | exact resolve eq4111 eq4149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111 eq4149
  have eq4338 : x = (M.op y x) ∨ x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq4313
  have eq4394 : x = (k x (M.op x x)) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1998 y
       have i₂ := eq4338
       grind)
    | exact superpose eq4338 eq1998
    | exact resolve eq1998 eq4338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998 eq4338
  have eq4417 : x = (k x y) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4394
       have i₂ := eq1731
       grind)
    | exact superpose eq1731 eq4394
    | exact resolve eq4394 eq1731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1731 eq4394
  have eq4426 : x = (τ (M.op (σ x) (σ y))) ∨ x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq4417
       have i₂ := eq2974
       grind)
    | exact superpose eq2974 eq4417
    | exact resolve eq4417 eq2974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974 eq4417
  have eq4427 : x = (τ (M.op (σ x) (σ y))) := by grind
  clear eq4426
  have eq4434 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4427 eq15
    | exact resolve eq15 eq4427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4427
  have eq4447 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4434
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4434
    | exact resolve eq4434 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4434
  have eq4449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1729 eq4447
    | exact resolve eq4447 eq1729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1729 eq4447
  have eq4451 : False := by grind
  exact eq4451

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation1701 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1701 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq49 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq63 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ (M.op X0 X0)) (k X1 (σ X0))
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq100 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) ∨ (τ X1) = X0 := by
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
  have eq101 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq98 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq98
    | (have j0 := eq98 X0 X1
       grind)
    | exact resolve eq98 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq357 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101 x y
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 x y
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq101 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq963 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq100 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq100
    | exact resolve eq100 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq1002 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq963 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq963
    | (have j0 := eq963 X0 X1
       grind)
    | exact resolve eq963 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq1563 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq357
       have i₂ := eq1002 y x
       grind)
    | exact superpose eq1002 eq357
    | (have j1 := eq1002 y x
       grind)
    | (have r₁ := eq357
       have r₂ := eq1002 y x
       grind)
    | (have r₁ := eq357
       have r₂ := eq1002 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq357
       have r₂ := eq1002 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq357 eq1002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357 eq1002
  have eq1564 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq1563
  have eq1740 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq367 (τ X1) (τ X0)
       have i₂ := eq49 X1 X0
       grind)
    | exact superpose eq49 eq367
    | (have j0 := eq367 (τ X1) (τ X0)
       grind)
    | exact resolve eq367 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1754 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1740 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq1740
    | (have j0 := eq1740 X0 X1
       grind)
    | exact resolve eq1740 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1740
  have eq1771 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1754 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1754
    | (have j0 := eq1754 X0 X1
       grind)
    | exact resolve eq1754 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754
  have eq1784 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1771 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1771
    | (have j0 := eq1771 X0 X1
       grind)
    | exact resolve eq1771 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771
  have eq1790 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1784 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1784
    | (have j0 := eq1784 X0 X1
       grind)
    | exact resolve eq1784 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1784
  have eq1794 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1790 X0 X1
       have i₂ := eq30 X1
       grind)
    | exact superpose eq30 eq1790
    | (have j0 := eq1790 X0 X1
       grind)
    | exact resolve eq1790 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1790
  have eq1798 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1794 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1794
    | (have j0 := eq1794 X0 X1
       grind)
    | exact resolve eq1794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1794
  have eq1799 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1798 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1798
    | (have j0 := eq1798 X0 X1
       grind)
    | exact resolve eq1798 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq15537 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1564
       grind)
    | exact superpose eq1564 eq16
    | exact resolve eq16 eq1564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq15538 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq15537
       have r₂ := eq22 x
       grind)
    | exact resolve eq15537 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15537
  have eq15541 : (M.op x x) ≠ (M.op x x) ∨ (k y x) = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq15538
       grind)
    | exact superpose eq15538 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15538
       grind)
    | exact resolve eq13 eq15538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15538
  have eq15571 : x = y ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq15541
  have eq27532 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15571
       grind)
    | exact superpose eq15571 eq16
    | exact resolve eq16 eq15571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15571
  have eq27533 : (k y x) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq27532
       have r₂ := eq22 x
       grind)
    | exact resolve eq27532 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27532
  have eq27542 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq367 x y
       have i₂ := eq27533
       grind)
    | exact superpose eq27533 eq367
    | (have j0 := eq367 x y
       grind)
    | exact resolve eq367 eq27533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq27533
  have eq27572 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq27542
  have eq27573 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
  clear eq27572
  have eq27762 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq27573
       grind)
    | exact superpose eq27573 eq16
    | exact resolve eq16 eq27573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27763 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq63 x (σ y)
       have i₂ := eq27573
       grind)
    | exact superpose eq27573 eq63
    | (have j0 := eq63 x (σ y)
       grind)
    | (have r₁ := eq63 x (σ y)
       have r₂ := eq27573
       grind)
    | exact resolve eq63 eq27573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq27573
  have eq27818 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq27763
  have eq27819 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq27818
  have eq27830 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq27819
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq27819
    | exact resolve eq27819 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27819
  have eq28335 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq27830
       grind)
    | exact superpose eq27830 eq10
    | exact resolve eq10 eq27830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27830
  have eq28534 : x = y ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq28335
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28335
    | exact resolve eq28335 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28335
  have eq28536 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28534
       grind)
    | exact superpose eq28534 eq16
    | exact resolve eq16 eq28534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28534
  have eq28537 : (σ (k y x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq28536
       have r₂ := eq22 x
       grind)
    | exact resolve eq28536 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28536
  have eq29054 : (k y x) = (τ (σ (M.op x x))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq28537
       grind)
    | exact superpose eq28537 eq10
    | exact resolve eq10 eq28537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28537
  have eq29255 : (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq29054
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq29054
    | exact resolve eq29054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29054
  have eq29276 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq1799 y x
       have i₂ := eq29255
       grind)
    | exact superpose eq29255 eq1799
    | (have j0 := eq1799 y x
       grind)
    | (have r₁ := eq1799 y x
       have r₂ := eq29255
       grind)
    | exact resolve eq1799 eq29255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799 eq29255
  have eq29297 : x = y ∨ (M.op x y) = (M.op x x) := by grind
  clear eq29276
  have eq29767 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29297
       grind)
    | exact superpose eq29297 eq16
    | exact resolve eq16 eq29297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29297
  have eq29770 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq29767
       have r₂ := eq22 x
       grind)
    | exact resolve eq29767 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29767
  have eq29771 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27762
       have i₂ := eq29770
       grind)
    | exact superpose eq29770 eq27762
    | exact resolve eq27762 eq29770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27762
  have eq29809 : (σ x) = (σ y) := by grind
  clear eq29771
  have eq30204 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29809
       grind)
    | exact superpose eq29809 eq16
    | exact resolve eq16 eq29809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29809
  have eq30406 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq30204
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq30204
    | exact resolve eq30204 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq30204
  have eq30407 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq30406
       have i₂ := eq29770
       grind)
    | exact superpose eq29770 eq30406
    | exact resolve eq30406 eq29770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29770 eq30406
  have eq30408 : False := by grind
  exact eq30408
