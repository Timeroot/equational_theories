import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3343`: `x ◇ y = y ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_y_pxy_Equation3343 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3343 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3343.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq76 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (τ X0) = (M.op X1 X1) := by
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
  clear eq19
  have eq479 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq68
  have eq871 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq74 X0 X1
       grind)
    | exact superpose eq74 eq10
    | (have j1 := eq74 X0 X1
       grind)
    | exact resolve eq10 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq7634 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq479 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq7636 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7634
  have eq7637 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7636 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7636
  have eq7818 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7637 (σ X0)
       grind)
    | exact superpose eq7637 eq15
    | exact resolve eq15 eq7637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7837 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq7818 X0
       have i₂ := eq7637 X0
       grind)
    | exact superpose eq7637 eq7818
    | exact resolve eq7818 eq7637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7637 eq7818
  have eq8505 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq8507 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq7837 X0
       grind)
    | exact superpose eq7837 eq26
    | exact resolve eq26 eq7837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8581 : ∀ X0 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8507 X0
       have i₂ := eq7837 (M.op X0 X0)
       grind)
    | exact superpose eq7837 eq8507
    | exact resolve eq8507 eq7837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8507
  have eq8583 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq8505 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq8505
    | exact resolve eq8505 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8505
  have eq8620 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8581 X0
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq8581
    | exact resolve eq8581 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq8581
  have eq8622 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  clear eq8583
  have eq10251 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq76
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq10821 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10251 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10251
    | (have j0 := eq10251 X0 X1
       grind)
    | exact resolve eq10251 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10251
  have eq55362 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq871 X1 X0
       grind)
    | exact superpose eq871 eq10
    | (have j1 := eq871 X1 X0
       grind)
    | exact resolve eq10 eq871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq55931 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55362 X0 X1
       have i₂ := eq7837 X0
       grind)
    | exact superpose eq7837 eq55362
    | (have j0 := eq55362 X0 X1
       grind)
    | exact resolve eq55362 eq7837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55362
  have eq56590 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55931 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq55931
    | (have j0 := eq55931 X0 X1
       grind)
    | exact resolve eq55931 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55931
  have eq57131 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56590 X0 X1
       have i₂ := eq7837 X1
       grind)
    | exact superpose eq7837 eq56590
    | (have j0 := eq56590 X0 X1
       grind)
    | exact resolve eq56590 eq7837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7837 eq56590
  have eq57504 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq57131 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq57131
    | (have j0 := eq57131 X0 X1
       grind)
    | exact resolve eq57131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57131
  have eq201829 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57504 y x
       grind)
    | exact superpose eq57504 eq16
    | (have j1 := eq57504 y x
       grind)
    | exact resolve eq16 eq57504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57504
  have eq201922 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq10821 x y
       grind)
    | (have r₁ := eq201829
       have r₂ := eq10821 x y
       grind)
    | exact resolve eq201829 eq10821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10821 eq201829
  have eq202582 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq8622 y
       have i₂ := eq201922
       grind)
    | exact superpose eq201922 eq8622
    | exact resolve eq8622 eq201922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8622 eq201922
  have eq202724 : y = (M.op x x) := by
    first
    | (have r₁ := eq202582
       have r₂ := eq16
       grind)
    | exact resolve eq202582 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202582
  have eq203744 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8620 x
       have i₂ := eq202724
       grind)
    | exact superpose eq202724 eq8620
    | exact resolve eq8620 eq202724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8620 eq202724
  have eq203912 : False := by grind
  exact eq203912

/-- `Equation3343`: `x ◇ y = y ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_y_pyx_Equation3343 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3343 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3343.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq100 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq80 (σ X0) (σ X1)
       grind)
    | exact superpose eq80 eq15
    | (have j1 := eq80 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq80 X0 (τ X1)
       grind)
    | exact superpose eq80 eq19
    | (have j1 := eq80 X0 (τ X1)
       grind)
    | exact resolve eq19 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq110 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq80
  have eq389 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq110 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq390 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq389 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq607 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq390 (σ X0)
       grind)
    | exact superpose eq390 eq15
    | exact resolve eq15 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq614 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq607 X0
       have i₂ := eq390 X0
       grind)
    | exact superpose eq390 eq607
    | exact resolve eq607 eq390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq607
  have eq977 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq614 X0
       grind)
    | exact superpose eq614 eq26
    | exact resolve eq26 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq995 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq977 X0
       have i₂ := eq614 (M.op X0 X0)
       grind)
    | exact superpose eq614 eq977
    | exact resolve eq977 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq1006 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq995 X0
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq995
    | exact resolve eq995 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq995
  have eq2325 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq102 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq102
    | exact resolve eq102 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq2450 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2325 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2325
    | (have j0 := eq2325 X0 X1
       grind)
    | exact resolve eq2325 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2325
  have eq4017 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq10
    | (have j1 := eq100 X0 X1
       grind)
    | exact resolve eq10 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq4164 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4017 X0 X1
       have i₂ := eq614 X0
       grind)
    | exact superpose eq614 eq4017
    | (have j0 := eq4017 X0 X1
       grind)
    | exact resolve eq4017 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq4017
  have eq4278 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4164 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4164
    | (have j0 := eq4164 X0 X1
       grind)
    | exact resolve eq4164 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4164
  have eq4718 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4278 x y
       grind)
    | exact superpose eq4278 eq16
    | (have j1 := eq4278 x y
       grind)
    | exact resolve eq16 eq4278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4278
  have eq4805 : y = (M.op x x) := by
    first
    | (have j1 := eq2450 y x
       grind)
    | (have r₁ := eq4718
       have r₂ := eq2450 y x
       grind)
    | exact resolve eq4718 eq2450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450 eq4718
  have eq5119 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1006 x
       have i₂ := eq4805
       grind)
    | exact superpose eq4805 eq1006
    | exact resolve eq1006 eq4805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq4805
  have eq5138 : False := by grind
  exact eq5138

/-- `Equation3343`: `x ◇ y = y ◇ (x ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_pyx_y_pyx_Equation3343 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3343 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3343.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
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
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op X0 X0)
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X1)) ∨ (k X1 (M.op X0 (M.op X0 X1))) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op X0 X1))
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq67 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq67 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq103 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq25 X0
       have i₂ := eq14 (M.op X0 X0) X1
       grind)
    | exact superpose eq14 eq25
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq25 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq14
    | (have j0 := eq14 X1 (M.op X0 X0)
       grind)
    | exact resolve eq14 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X1 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq109 X0 X1
       have j1 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq109 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq109 X0 (M.op X0 (M.op X0 (M.op X0 X0)))
       have r₂ := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq109 X0 X0
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | exact resolve eq109 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq114 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq103 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq103 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq191 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (k X2 X1) = (M.op X1 X2) ∨ (M.op X2 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1
       have i₂ := eq114 X1 X0
       grind)
    | (have i₁ := eq14 X0 X0
       have i₂ := eq114 X0 X0
       grind)
    | exact superpose eq114 eq14
    | (have j0 := eq14 X2 X1
       have j1 := eq114 X2 X1
       grind)
    | exact resolve eq14 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq201 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X2 ∨ (k X2 X1) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq191 X0 X1 X2
       have j1 := eq12 X2 X1
       grind)
    | (have r₁ := eq191 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq191 X0 X1 (M.op X0 (M.op X0 X1))
       have r₂ := eq12 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq191 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq191 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq269 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (M.op X0 X0)
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq34
    | (have j0 := eq34 X0 X0
       grind)
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 X0
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq34
    | (have j1 := eq71 X0 X0
       grind)
    | exact resolve eq34 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq71
  have eq273 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq271 X0 X0
       have j1 := eq201 X0 X0 (k X0 X0)
       grind)
    | (have r₁ := eq271 x X0
       have r₂ := eq201 X0 x x
       grind)
    | (have r₁ := eq271 (M.op X0 X1) X1
       have r₂ := eq201 X0 X1 (M.op X1 (M.op X0 X1))
       grind)
    | exact resolve eq271 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq271
  have eq274 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq269 X0
       have j1 := eq111 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq269 X0
       have r₂ := eq111 X0 (M.op X0 X0)
       grind)
    | exact resolve eq269 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq269
  have eq278 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq274 X0
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq274
    | exact resolve eq274 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq274
  have eq380 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq63 X1 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq393 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq380 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380
  have eq413 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq393
    | (have j0 := eq393 X0 X1
       grind)
    | exact resolve eq393 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq414 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq413 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq467 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq273 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq468 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq467 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq528 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq468 (σ X0)
       grind)
    | exact superpose eq468 eq15
    | exact resolve eq15 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq528 X0
       have i₂ := eq468 X0
       grind)
    | exact superpose eq468 eq528
    | exact resolve eq528 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq528
  have eq719 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq278 (σ X0)
       have i₂ := eq535 X0
       grind)
    | exact superpose eq535 eq278
    | exact resolve eq278 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq719 X0
       have i₂ := eq15 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq15 eq719
    | exact resolve eq719 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq719
  have eq734 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq723 X0
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq723
    | exact resolve eq723 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq723
  have eq2188 : ∀ X0 X1 : G, (σ X1) = (M.op X0 X0) ∨ (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq414 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq414
    | exact resolve eq414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2230 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq414 X0 X1
       grind)
    | exact superpose eq414 eq10
    | (have j1 := eq414 X0 X1
       grind)
    | exact resolve eq10 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq2346 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2230 X0 X1
       have i₂ := eq535 X0
       grind)
    | exact superpose eq535 eq2230
    | (have j0 := eq2230 X0 X1
       grind)
    | exact resolve eq2230 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535 eq2230
  have eq2365 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2188 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq2188
    | (have j0 := eq2188 X0 X1
       grind)
    | exact resolve eq2188 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2188
  have eq2428 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2346 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq2346
    | (have j0 := eq2346 X0 X1
       grind)
    | exact resolve eq2346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2346
  have eq2756 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2365 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2365
    | exact resolve eq2365 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq3397 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2428 x y
       grind)
    | exact superpose eq2428 eq16
    | (have j1 := eq2428 x y
       grind)
    | exact resolve eq16 eq2428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428
  have eq3808 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3397
       have i₂ := eq2756 y x
       grind)
    | exact superpose eq2756 eq3397
    | (have j1 := eq2756 y x
       grind)
    | exact resolve eq3397 eq2756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2756 eq3397
  have eq3812 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq3808
  have eq3813 : y = (M.op x x) := by grind
  clear eq3812
  have eq4031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq734 x
       have i₂ := eq3813
       grind)
    | exact superpose eq3813 eq734
    | exact resolve eq734 eq3813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq734 eq3813
  have eq4053 : False := by grind
  exact eq4053

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pxx_x_pxy_Equation3352 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq118 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq121 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
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
       have r₂ := eq14 (M.op X0 X1) (M.op X0 X0)
       grind)
    | exact resolve eq118 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq188 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq121 (σ X0) (σ X1)
       grind)
    | exact superpose eq121 eq15
    | (have j1 := eq121 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq121 (τ X0) X1
       grind)
    | exact superpose eq121 eq18
    | (have j1 := eq121 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq121
  have eq812 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq190 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq190
    | exact resolve eq190 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq853 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq812 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq812
    | (have j0 := eq812 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq812 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq2633 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq188 x y
       grind)
    | exact superpose eq188 eq16
    | (have j1 := eq188 x y
       grind)
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq2759 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2633
       have i₂ := eq853 x y
       grind)
    | exact superpose eq853 eq2633
    | (have j1 := eq853 (σ x) (σ y)
       grind)
    | (have r₁ := eq2633
       have r₂ := eq853 x y
       grind)
    | (have r₁ := eq2633
       have r₂ := eq853 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2633
       have r₂ := eq853 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2633 eq853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq853 eq2633
  have eq2760 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2759
  have eq2815 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2760
       grind)
    | exact superpose eq2760 eq10
    | exact resolve eq10 eq2760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq2863 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2815
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2815
    | exact resolve eq2815 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2815
  have eq2864 : x = y := by grind
  clear eq2863
  have eq3144 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2864
       grind)
    | exact superpose eq2864 eq16
    | exact resolve eq16 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864
  have eq3145 : False := by grind
  exact eq3145

/-- `Equation3355`: `x ◇ y = y ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pxy_Equation3355 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3355 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3355.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq26 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq111 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq83 (σ X1) (σ X0)
       grind)
    | exact superpose eq83 eq15
    | (have j1 := eq83 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq83 X1 (τ X0)
       grind)
    | exact superpose eq83 eq19
    | (have j1 := eq83 X1 (τ X0)
       grind)
    | exact resolve eq19 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq122 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  clear eq83
  have eq331 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq122 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq332 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq534 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq332 (σ X0)
       grind)
    | exact superpose eq332 eq15
    | exact resolve eq15 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq534 X0
       have i₂ := eq332 X0
       grind)
    | exact superpose eq332 eq534
    | exact resolve eq534 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq534
  have eq857 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq541 X0
       grind)
    | exact superpose eq541 eq26
    | exact resolve eq26 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq880 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq861 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq861
    | exact resolve eq861 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq891 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq880
  have eq1906 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq113 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq113
    | exact resolve eq113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq2038 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1906 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1906
    | (have j0 := eq1906 X0 X1
       grind)
    | exact resolve eq1906 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906
  have eq3164 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq111 X1 X0
       grind)
    | exact superpose eq111 eq10
    | (have j1 := eq111 X1 X0
       grind)
    | exact resolve eq10 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq3296 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3164 X0 X1
       have i₂ := eq541 X0
       grind)
    | exact superpose eq541 eq3164
    | (have j0 := eq3164 X0 X1
       grind)
    | exact resolve eq3164 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq3164
  have eq3403 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3296 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3296
    | (have j0 := eq3296 X0 X1
       grind)
    | exact resolve eq3296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3296
  have eq3862 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3403 y x
       grind)
    | exact superpose eq3403 eq16
    | (have j1 := eq3403 y x
       grind)
    | exact resolve eq16 eq3403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3403
  have eq3931 : x = (M.op y y) := by
    first
    | (have j1 := eq2038 x y
       grind)
    | (have r₁ := eq3862
       have r₂ := eq2038 x y
       grind)
    | exact resolve eq3862 eq2038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2038 eq3862
  have eq4189 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq891 y
       have i₂ := eq3931
       grind)
    | exact superpose eq3931 eq891
    | exact resolve eq891 eq3931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq4193 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq26 y y
       have i₂ := eq3931
       grind)
    | exact superpose eq3931 eq26
    | exact resolve eq26 eq3931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq4207 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq4189
       have i₂ := eq4193
       grind)
    | exact superpose eq4193 eq4189
    | exact resolve eq4189 eq4193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4189 eq4193
  have eq41851 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq857 y
       have i₂ := eq3931
       grind)
    | exact superpose eq3931 eq857
    | exact resolve eq857 eq3931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857 eq3931
  have eq42009 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq41851
       have i₂ := eq4207
       grind)
    | exact superpose eq4207 eq41851
    | exact resolve eq41851 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4207 eq41851
  have eq42063 : False := by grind
  exact eq42063

/-- `Equation3355`: `x ◇ y = y ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pyx_Equation3355 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3355 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3355.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq26 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq99 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq470 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq71 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq475 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq470 X0 X1
       have j1 := eq99 X1 X0
       grind)
    | (have r₁ := eq470 X0 X0
       have r₂ := eq99 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq470 X0 X1
       have r₂ := eq99 X0 X1
       grind)
    | (have r₁ := eq470 X1 X0
       have r₂ := eq99 X0 X1
       grind)
    | exact resolve eq470 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq470
  have eq510 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq1426 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq510 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq1427 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1426 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426
  have eq1634 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1427 (σ X0)
       grind)
    | exact superpose eq1427 eq15
    | exact resolve eq15 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1645 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1634 X0
       have i₂ := eq1427 X0
       grind)
    | exact superpose eq1427 eq1634
    | exact resolve eq1634 eq1427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427 eq1634
  have eq2204 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq2229 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq475 X1 (σ X0)
       have i₂ := eq1645 X0
       grind)
    | exact superpose eq1645 eq475
    | (have j0 := eq475 X1 (σ X0)
       grind)
    | exact resolve eq475 eq1645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645
  have eq2237 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2204 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq2204
    | exact resolve eq2204 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204
  have eq2248 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq2237
  have eq6336 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq2229 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq2229 X0 (σ X0)
       grind)
    | exact superpose eq2229 eq10
    | (have j1 := eq2229 X1 X0
       grind)
    | exact resolve eq10 eq2229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2229
  have eq7816 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq6336 (σ X1) X0
       grind)
    | exact superpose eq6336 eq15
    | (have j1 := eq6336 (σ X1) X0
       grind)
    | exact resolve eq15 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6336
  have eq7846 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7816 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7816
    | (have j0 := eq7816 X0 X1
       grind)
    | exact resolve eq7816 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7816
  have eq11133 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7846 x y
       grind)
    | exact superpose eq7846 eq16
    | (have j1 := eq7846 x y
       grind)
    | exact resolve eq16 eq7846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7846
  have eq11777 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11133
       have i₂ := eq475 y x
       grind)
    | exact superpose eq475 eq11133
    | (have j1 := eq475 y x
       grind)
    | exact resolve eq11133 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq11133
  have eq11787 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq11777
  have eq11788 : y = (M.op x x) := by grind
  clear eq11787
  have eq12339 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2248 x
       have i₂ := eq11788
       grind)
    | exact superpose eq11788 eq2248
    | exact resolve eq2248 eq11788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248 eq11788
  have eq12384 : False := by grind
  exact eq12384

/-- `Equation3355`: `x ◇ y = y ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_y_pxy_Equation3355 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3355 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3355.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 (M.op X1 X0))) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq26 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq100 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq26 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq26 X0 X1
       have i₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact superpose eq14 eq26
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq26 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq72 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq474 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq469 X0 X1
       have j1 := eq100 X1 X0
       grind)
    | (have r₁ := eq469 X0 X0
       have r₂ := eq100 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq469 X0 X1
       have r₂ := eq100 X0 X1
       grind)
    | (have r₁ := eq469 X1 X0
       have r₂ := eq100 X0 X1
       grind)
    | exact resolve eq469 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq469
  have eq509 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq1064 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq509 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq1065 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1064 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1256 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1065 (σ X0)
       grind)
    | exact superpose eq1065 eq15
    | exact resolve eq15 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1267 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1256 X0
       have i₂ := eq1065 X0
       grind)
    | exact superpose eq1065 eq1256
    | exact resolve eq1256 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065 eq1256
  have eq1728 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq1745 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq474 X1 (σ X0)
       have i₂ := eq1267 X0
       grind)
    | exact superpose eq1267 eq474
    | (have j0 := eq474 X1 (σ X0)
       grind)
    | exact resolve eq474 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq1752 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1728 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq1728
    | exact resolve eq1728 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq1762 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq1752
  have eq1764 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1762 X0
       have i₂ := eq26 X0 X0
       grind)
    | exact superpose eq26 eq1762
    | exact resolve eq1762 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1762
  have eq9319 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq1745 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq1745 X0 (σ X0)
       grind)
    | exact superpose eq1745 eq10
    | (have j1 := eq1745 X1 X0
       grind)
    | exact resolve eq10 eq1745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1745
  have eq11546 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq9319 (σ X0) X1
       grind)
    | exact superpose eq9319 eq15
    | (have j1 := eq9319 (σ X0) X1
       grind)
    | exact resolve eq15 eq9319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9319
  have eq11578 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11546 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq11546
    | (have j0 := eq11546 X0 X1
       grind)
    | exact resolve eq11546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11546
  have eq14477 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11578 x y
       grind)
    | exact superpose eq11578 eq16
    | (have j1 := eq11578 x y
       grind)
    | exact resolve eq16 eq11578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11578
  have eq15147 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq14477
       have i₂ := eq474 x y
       grind)
    | exact superpose eq474 eq14477
    | (have j1 := eq474 x y
       grind)
    | exact resolve eq14477 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq14477
  have eq15154 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq15147
  have eq15155 : x = (M.op y y) := by grind
  clear eq15154
  have eq15403 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq1764 y
       have i₂ := eq15155
       grind)
    | exact superpose eq15155 eq1764
    | exact resolve eq1764 eq15155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1764
  have eq15416 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq26 y y
       have i₂ := eq15155
       grind)
    | exact superpose eq15155 eq26
    | exact resolve eq26 eq15155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15155
  have eq15470 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15403
       have i₂ := eq15416
       grind)
    | exact superpose eq15416 eq15403
    | exact resolve eq15403 eq15416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15403 eq15416
  have eq15481 : False := by grind
  exact eq15481

/-- `Equation3385`: `x ◇ y = z ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_y_pxy_x_pxy_Equation3385 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3385 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3385.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq22 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k (τ X0) X1) X2
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op X1 X3)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X0 (M.op X1 X3))
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X0 (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq14 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq76 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq74 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq74 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq74 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq74 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq86 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq76 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq90 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op X0 X1) (M.op X3 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X3 (M.op X2 X0) (M.op X1 X2)
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op (M.op X2 X0) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 X2
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 X3) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X3 X0) (M.op X1 X3)
       have i₂ := eq25 X1 X3 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X0) X1
       have i₂ := eq25 X0 X0 X0
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq25 X0 X0 X0
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq98 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq104 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq90 X0 X1 X2 X3
       have i₂ := eq96 X1 (M.op X3 (M.op X2 X0)) X0
       grind)
    | (have i₁ := eq90 X0 X1 X2 X0
       have i₂ := eq96 X0 (M.op X2 X0) (M.op X0 X1)
       grind)
    | exact superpose eq96 eq90
    | exact resolve eq90 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq108 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X3 (M.op X2 X0)))) = (M.op X1 (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq104 X0 X1 X2 X3
       have i₂ := eq96 X2 X3 X1
       grind)
    | (have i₁ := eq104 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq96 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq96 eq104
    | exact resolve eq104 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq15
    | exact resolve eq15 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq86 (τ X0)
       grind)
    | exact superpose eq86 eq19
    | exact resolve eq19 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq116
    | exact resolve eq116 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq112
    | exact resolve eq112 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq123 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq117
    | exact resolve eq117 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq160 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X0 (M.op X1 X2) X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op X1 (M.op X2 X3)) (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X1 X2 (M.op X2 X0) X3
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq25 X4 (M.op X2 (M.op X3 X1)) (M.op X0 (M.op X2 X3))
       have i₂ := eq24 X2 X3 X0 X1
       grind)
    | exact superpose eq24 eq25
    | exact resolve eq25 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq171 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op (M.op X0 (M.op X3 X4)) (M.op X2 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X2 (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X3 X4))
       have i₂ := eq24 X3 X4 X0 X1
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op (M.op X3 X4) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq171 X0 X1 X2 X3 X4
       have i₂ := eq96 (M.op X3 X4) (M.op X2 (M.op X0 X1)) X0
       grind)
    | (have i₁ := eq171 X0 X1 X0 X3 X4
       have i₂ := eq96 X0 (M.op X0 X1) (M.op X0 (M.op X3 X4))
       grind)
    | exact superpose eq96 eq171
    | exact resolve eq171 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq180 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X1 (M.op X4 (M.op X2 (M.op X3 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq170 X0 X1 X2 X3 X4
       have i₂ := eq96 X1 (M.op X4 (M.op X2 (M.op X3 X1))) X0
       grind)
    | (have i₁ := eq170 X0 X1 X2 X3 X0
       have i₂ := eq96 X0 (M.op X2 (M.op X3 X1)) (M.op X0 X1)
       grind)
    | exact superpose eq96 eq170
    | exact resolve eq170 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq186 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X0) X3) = (M.op (M.op X2 X3) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq163 X0 x X2 X3
       have i₂ := eq25 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq25 eq163
    | exact resolve eq163 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq189 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op (M.op X1 X2) X3) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq160 X0 X1 X2 X3
       have i₂ := eq96 (M.op (M.op X1 X2) X3) (M.op X0 X1) X0
       grind)
    | (have i₁ := eq160 X0 X1 X2 X3
       have i₂ := eq96 X0 X1 (M.op X0 (M.op (M.op X1 X2) X3))
       grind)
    | exact superpose eq96 eq160
    | exact resolve eq160 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq207 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X1))) = (M.op X0 (M.op X3 (M.op X4 (M.op X2 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq179 X0 X1 X2 X3 X4
       have i₂ := eq96 X4 (M.op X2 (M.op X0 X1)) X3
       grind)
    | (have i₁ := eq179 X0 X1 X0 X3 X4
       have i₂ := eq96 X0 (M.op X0 X1) (M.op X3 X4)
       grind)
    | exact superpose eq96 eq179
    | exact resolve eq179 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq208 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X3)) X4) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq180 X0 x X2 X3 X4
       have i₂ := eq108 x X4 X3 X2
       grind)
    | exact superpose eq108 eq180
    | exact resolve eq180 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq180
  have eq214 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X2 X0) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq186 X0 X2 X3
       have i₂ := eq96 X3 X0 X2
       grind)
    | (have i₁ := eq186 (M.op X0 x) X2 X3
       have i₂ := eq96 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq96 eq186
    | exact resolve eq186 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq217 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq189 X0 X1 X2 X3
       have i₂ := eq96 X3 (M.op X0 X1) (M.op X1 X2)
       grind)
    | (have i₁ := eq189 X0 X1 X2 X3
       have i₂ := eq96 X0 X1 (M.op (M.op X1 X2) X3)
       grind)
    | exact superpose eq96 eq189
    | exact resolve eq189 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq233 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 X3) X4)) = (M.op X0 (M.op X4 (M.op X3 X2))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq208 X0 X2 X3 X4
       have i₂ := eq96 (M.op X2 X3) X4 X0
       grind)
    | (have i₁ := eq208 X0 X2 X3 (M.op X0 x)
       have i₂ := eq96 X0 x (M.op X0 (M.op X2 X3))
       grind)
    | exact superpose eq96 eq208
    | exact resolve eq208 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq241 : ∀ X0 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X3 (M.op X2 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq217 X0 x X2 X3
       have i₂ := eq97 X0 x X3 X2
       grind)
    | exact superpose eq97 eq217
    | exact resolve eq217 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq250 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op X4 (M.op X3 X2))) = (M.op X0 (M.op X2 (M.op X3 X4))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq233 X0 X4 X3 X2
       have i₂ := eq96 X3 X2 X4
       grind)
    | (have i₁ := eq233 X0 X2 X3 (M.op X0 x)
       have i₂ := eq96 X0 x (M.op X2 X3)
       grind)
    | exact superpose eq96 eq233
    | exact resolve eq233 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq280 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq86 (τ X0)
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq86
    | exact resolve eq86 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq280 X0
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq280
    | exact resolve eq280 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq506 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq507 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq506 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq549 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op X2 X0) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq96 (M.op X1 X2) X3 (M.op X2 X0)
       have i₂ := eq25 X1 X2 X0
       grind)
    | exact superpose eq25 eq96
    | exact resolve eq96 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ X0) X1)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96 (σ X0) X1 (σ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq96
    | exact resolve eq96 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq565 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X4 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X4 (M.op X0 X1) X3 X2
       have i₂ := eq96 X1 X2 X0
       grind)
    | exact superpose eq96 eq24
    | exact resolve eq24 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op (M.op X2 (M.op X3 X4)) (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq24 X2 X3 (M.op X0 X1) X4
       have i₂ := eq96 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq96 eq24
    | exact resolve eq24 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq574 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X0 (M.op X1 (M.op X2 (M.op X3 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X3 (M.op X0 X1)
       have i₂ := eq96 X1 (M.op X2 (M.op X3 (M.op X0 X1))) X0
       grind)
    | exact superpose eq96 eq9
    | exact resolve eq9 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X1 (M.op X2 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq574 x X1 X2 X3
       have i₂ := eq207 x X1 X3 X1 X2
       grind)
    | exact superpose eq207 eq574
    | exact resolve eq574 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq587 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X2 (M.op (M.op X3 X4) (M.op X0 (M.op X1 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq571 X0 X1 X2 X3 X4
       have i₂ := eq96 (M.op X3 X4) (M.op X0 (M.op X1 (M.op X2 X3))) X2
       grind)
    | (have i₁ := eq571 X0 X1 X2 X3 X4
       have i₂ := eq96 X0 (M.op X1 (M.op X2 X3)) (M.op X2 (M.op X3 X4))
       grind)
    | exact superpose eq96 eq571
    | exact resolve eq571 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq592 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X4 (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 X1))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq565 X0 X1 X2 X3 X4
       have i₂ := eq96 (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X4 (M.op X0 X1))) X4
       grind)
    | (have i₁ := eq565 X0 X1 X2 X0 X4
       have i₂ := eq96 X0 (M.op X4 (M.op X0 X1)) (M.op X4 (M.op X0 (M.op X1 X2)))
       grind)
    | exact superpose eq96 eq565
    | exact resolve eq565 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq602 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X0 (M.op (M.op X1 X2) X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq549 X0 X1 X2 X3
       have i₂ := eq96 X0 (M.op (M.op X1 X2) X3) X2
       grind)
    | (have i₁ := eq549 X0 X1 X2 X1
       have i₂ := eq96 (M.op X1 X2) X1 (M.op X2 X0)
       grind)
    | exact superpose eq96 eq549
    | exact resolve eq549 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq610 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 (M.op (M.op X3 X4) (M.op X0 X3))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq587 X0 X1 x X3 X4
       have i₂ := eq207 x X3 X1 (M.op X3 X4) X0
       grind)
    | exact superpose eq207 eq587
    | exact resolve eq587 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq612 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op X4 (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 X1)))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq592 X0 X1 X2 X3 X4
       have i₂ := eq96 (M.op X1 X2) (M.op X3 (M.op X4 (M.op X0 X1))) X0
       grind)
    | (have i₁ := eq592 X0 X1 X2 X0 X4
       have i₂ := eq96 X0 (M.op X4 (M.op X0 X1)) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq96 eq592
    | exact resolve eq592 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq618 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq602 X0 X1 X2 X3
       have i₂ := eq96 X2 X3 X1
       grind)
    | (have i₁ := eq602 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq96 X0 X1 (M.op X1 X2)
       grind)
    | exact superpose eq96 eq602
    | exact resolve eq602 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq625 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X4) = (M.op X1 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq610 X0 X1 X3 X4
       have i₂ := eq250 X1 X3 X0 (M.op X3 X4)
       grind)
    | (have i₁ := eq610 X0 X1 X3 X4
       have i₂ := eq250 X1 (M.op X3 X4) X0 X3
       grind)
    | exact superpose eq250 eq610
    | exact resolve eq610 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq626 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq612 X0 X1 X2 X3 x
       have i₂ := eq207 x (M.op X0 X1) X3 X0 (M.op X1 X2)
       grind)
    | exact superpose eq207 eq612
    | exact resolve eq612 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq612
  have eq631 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (M.op X2 (M.op X0 (M.op X1 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq618 X0 X1 X2 X3
       have i₂ := eq96 X1 X3 X0
       grind)
    | (have i₁ := eq618 X0 X1 X2 (M.op X0 X1)
       have i₂ := eq96 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq96 eq618
    | exact resolve eq618 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq634 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op X1 (M.op X3 (M.op X0 (M.op X3 X4)))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq625 X0 X1 X3 X4
       have i₂ := eq96 X1 X4 X0
       grind)
    | (have i₁ := eq625 X0 X1 X3 (M.op X0 X1)
       have i₂ := eq96 X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq96 eq625
    | exact resolve eq625 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq635 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 (M.op X1 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq626 X0 X1 X2 X3
       have i₂ := eq250 X0 X1 X0 (M.op X1 X2)
       grind)
    | (have i₁ := eq626 X0 X1 X2 X3
       have i₂ := eq250 X0 (M.op X1 X2) X0 X1
       grind)
    | exact superpose eq250 eq626
    | exact resolve eq626 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq626
  have eq638 : ∀ X1 X2 X3 : G, (M.op X3 X2) = (M.op X1 (M.op X3 (M.op X1 X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq635 x X1 X2 X3
       have i₂ := eq634 X1 X3 x (M.op X1 X2)
       grind)
    | (have i₁ := eq635 X1 X1 X2 x
       have i₂ := eq634 x X1 X3 (M.op X1 (M.op X1 (M.op X1 X2)))
       grind)
    | exact superpose eq634 eq635
    | exact resolve eq635 eq634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq635
  have eq1167 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X1 X0 X2
       have i₂ := eq214 X2 X0 (M.op X1 X0)
       grind)
    | exact superpose eq214 eq25
    | exact resolve eq25 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op X0 (M.op (M.op X1 (M.op X0 X2)) (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq24 X0 X2 X1 X3
       have i₂ := eq214 (M.op X2 X3) X0 (M.op X1 (M.op X0 X2))
       grind)
    | exact superpose eq214 eq24
    | exact resolve eq24 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1175 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq25 X3 (M.op X0 X2) X1
       have i₂ := eq214 X2 X0 X1
       grind)
    | exact superpose eq214 eq25
    | exact resolve eq25 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op X0 (M.op (M.op X1 X2) (M.op X3 (M.op X0 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1175 X0 X1 X2 X3
       have i₂ := eq96 (M.op X1 X2) (M.op X3 (M.op X0 X2)) X0
       grind)
    | (have i₁ := eq1175 X0 X1 X2 X0
       have i₂ := eq96 X0 (M.op X0 X2) (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq96 eq1175
    | exact resolve eq1175 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1175
  have eq1218 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op X0 (M.op X1 (M.op (M.op X0 X2) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1168 X0 X1 X2 X3
       have i₂ := eq96 (M.op X0 X2) (M.op X2 X3) X1
       grind)
    | (have i₁ := eq1168 X0 X1 X0 X1
       have i₂ := eq96 X0 X1 (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq96 eq1168
    | exact resolve eq1168 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168
  have eq1219 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1167 X0 X1 X2
       have i₂ := eq96 X0 X2 X1
       grind)
    | (have i₁ := eq1167 X0 X1 (M.op X0 X1)
       have i₂ := eq96 X0 X1 (M.op X1 X0)
       grind)
    | exact superpose eq96 eq1167
    | exact resolve eq1167 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1167
  have eq1254 : ∀ X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op X1 X2) (M.op X3 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1213 x X1 X2 X3
       have i₂ := eq631 (M.op X1 X2) X3 x X2
       grind)
    | exact superpose eq631 eq1213
    | exact resolve eq1213 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq1213
  have eq1257 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op X0 (M.op X1 (M.op X0 (M.op X2 (M.op X2 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1218 X0 X1 X2 X3
       have i₂ := eq96 X2 (M.op X2 X3) X0
       grind)
    | (have i₁ := eq1218 X0 X1 X0 X1
       have i₂ := eq96 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq96 eq1218
    | exact resolve eq1218 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq1284 : ∀ X1 X2 X3 : G, (M.op X1 X3) = (M.op X1 (M.op X2 (M.op X3 X2))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1254 X1 X2 X3
       have i₂ := eq96 X2 (M.op X3 X2) X1
       grind)
    | (have i₁ := eq1254 X1 X1 x
       have i₂ := eq96 x X1 (M.op X1 X1)
       grind)
    | exact superpose eq96 eq1254
    | exact resolve eq1254 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1287 : ∀ X1 X2 X3 : G, (M.op X1 X3) = (M.op X1 (M.op X2 (M.op X2 X3))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq1257 x X1 X2 X3
       have i₂ := eq638 x (M.op X2 (M.op X2 X3)) X1
       grind)
    | exact superpose eq638 eq1257
    | exact resolve eq1257 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1728 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 x
       have i₂ := eq241 x X1 X0
       grind)
    | exact superpose eq241 eq9
    | exact resolve eq9 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2042 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq214 X0 X1 X2
       have i₂ := eq1728 X1 X0
       grind)
    | (have i₁ := eq214 X0 X1 X2
       have i₂ := eq1728 X0 X1
       grind)
    | exact superpose eq1728 eq214
    | exact resolve eq214 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq2171 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq507 X0 (τ X1)
       grind)
    | exact superpose eq507 eq19
    | (have j1 := eq507 X0 (τ X1)
       grind)
    | exact resolve eq19 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2412 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq584 (M.op X0 X1) X1 X2
       have i₂ := eq584 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq584 eq584
    | exact resolve eq584 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2684 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X0) X0 X1
       have i₂ := eq86 (σ X0)
       grind)
    | exact superpose eq86 eq22
    | exact resolve eq22 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2724 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k (τ (σ X0)) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2684 X0 X1
       have i₂ := eq99 (σ X0) (σ X1)
       grind)
    | exact superpose eq99 eq2684
    | exact resolve eq2684 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2684
  have eq2733 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2724 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2724
    | exact resolve eq2724 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2724
  have eq2738 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2733 X0 X1
       have i₂ := eq86 X0
       grind)
    | exact superpose eq86 eq2733
    | exact resolve eq2733 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2733
  have eq2741 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2738 X0 X1
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq2738
    | exact resolve eq2738 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738
  have eq2742 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (M.op X0 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2741 X0 X1
       have i₂ := eq96 X0 X1 X0
       grind)
    | (have i₁ := eq2741 X0 (M.op X0 X1)
       have i₂ := eq96 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq96 eq2741
    | exact resolve eq2741 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2741
  have eq2743 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ X0) (M.op (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2742 X0 X1
       have i₂ := eq96 (σ X0) (σ X1) (σ X0)
       grind)
    | exact superpose eq96 eq2742
    | exact resolve eq2742 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2742
  have eq2744 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X1))) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2743 X0 X1
       have i₂ := eq552 X0 (σ X1)
       grind)
    | exact superpose eq552 eq2743
    | exact resolve eq2743 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq2743
  have eq2773 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq638 X2 (M.op X0 X1) X0
       have i₂ := eq638 X0 X1 X2
       grind)
    | exact superpose eq638 eq638
    | exact resolve eq638 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2797 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq584 X1 X0 X0
       have i₂ := eq638 X0 X1 X1
       grind)
    | exact superpose eq638 eq584
    | exact resolve eq584 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584
  have eq3166 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq283 X1
       have i₂ := eq2797 (τ X1) X0
       grind)
    | (have i₁ := eq283 X1
       have i₂ := eq2797 X0 (τ X1)
       grind)
    | exact superpose eq2797 eq283
    | exact resolve eq283 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq3167 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq123 X1
       have i₂ := eq2797 (τ X1) X0
       grind)
    | (have i₁ := eq123 X1
       have i₂ := eq2797 X0 (τ X1)
       grind)
    | exact superpose eq2797 eq123
    | exact resolve eq123 eq2797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3365 : ∀ X0 X1 X2 : G, (τ X0) = (M.op X1 X1) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3166 X1 X2
       have i₂ := eq507 X2 X0
       grind)
    | (have i₁ := eq3166 X0 X1
       have i₂ := eq507 X0 (M.op X1 X1)
       grind)
    | exact superpose eq507 eq3166
    | (have j1 := eq507 X2 X0
       grind)
    | exact resolve eq3166 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq3385 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (τ (M.op X0 X0)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 X1 X1
       have i₂ := eq3166 X1 X0
       grind)
    | exact superpose eq3166 eq25
    | exact resolve eq25 eq3166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq3429 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (σ X2)) = (σ (k (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 (M.op X1 X1) X2
       have i₂ := eq3166 X0 X1
       grind)
    | exact superpose eq3166 eq18
    | exact resolve eq18 eq3166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3432 : ∀ X0 X1 X2 : G, (τ (k (M.op X1 X1) X2)) = (k (M.op X0 X0) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X2 (M.op X1 X1)
       have i₂ := eq3166 X0 X1
       grind)
    | exact superpose eq3166 eq34
    | exact resolve eq34 eq3166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3438 : ∀ X0 X1 X2 : G, (τ (k (M.op X1 X1) X2)) = (M.op (M.op X0 X0) (τ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3432 X0 X1 X2
       have i₂ := eq99 X0 (τ X2)
       grind)
    | exact superpose eq99 eq3432
    | exact resolve eq3432 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432
  have eq3439 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (σ X2)) = (σ (M.op (M.op X0 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3429 X0 X1 X2
       have i₂ := eq99 X0 X2
       grind)
    | exact superpose eq99 eq3429
    | exact resolve eq3429 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3429
  have eq3475 : ∀ X0 X1 X2 : G, (τ (k (M.op X1 X1) X2)) = (M.op X0 (M.op X0 (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3438 X0 X1 X2
       have i₂ := eq96 X0 (τ X2) X0
       grind)
    | exact superpose eq96 eq3438
    | exact resolve eq3438 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438
  have eq3476 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (σ X2)) = (σ (M.op X0 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3439 X0 X1 X2
       have i₂ := eq96 X0 X2 X0
       grind)
    | (have i₁ := eq3439 X0 X1 (M.op X0 X1)
       have i₂ := eq96 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq96 eq3439
    | exact resolve eq3439 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439
  have eq3491 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (τ X2))) = (τ (M.op (M.op X1 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3475 X0 X1 X2
       have i₂ := eq99 X1 X2
       grind)
    | exact superpose eq99 eq3475
    | exact resolve eq3475 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3475
  have eq3492 : ∀ X0 X1 X2 : G, (σ (M.op X0 (M.op X0 X2))) = (M.op (M.op X1 X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3476 X0 X1 X2
       have i₂ := eq99 X1 (σ X2)
       grind)
    | exact superpose eq99 eq3476
    | exact resolve eq3476 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq3476
  have eq3496 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (τ X2))) = (τ (M.op X1 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3491 X0 X1 X2
       have i₂ := eq96 X1 X2 X1
       grind)
    | (have i₁ := eq3491 X0 X1 (M.op X0 X1)
       have i₂ := eq96 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq96 eq3491
    | exact resolve eq3491 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3491
  have eq3497 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (σ X2))) = (σ (M.op X0 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3492 X0 X1 X2
       have i₂ := eq96 X1 (σ X2) X1
       grind)
    | exact superpose eq96 eq3492
    | exact resolve eq3492 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq3492
  have eq3513 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (τ (M.op X0 X0)) (M.op X1 (M.op X3 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq97 X3 X2 X1 X2
       have i₂ := eq3166 X2 X0
       grind)
    | exact superpose eq3166 eq97
    | exact resolve eq97 eq3166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq3166
  have eq3760 : ∀ X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op (M.op X3 X2) X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq3513 x X1 X2 X3
       have i₂ := eq3385 x (M.op X3 X2) X1
       grind)
    | exact superpose eq3385 eq3513
    | exact resolve eq3513 eq3385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385 eq3513
  have eq4128 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq638 X2 X2 X1
       have i₂ := eq3167 X0 X2
       grind)
    | exact superpose eq3167 eq638
    | exact resolve eq638 eq3167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq3167
  have eq271203 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3365 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq3365 eq15
    | (have j1 := eq3365 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq3365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq271219 : ∀ X0 X1 X2 : G, (M.op X2 X2) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq271203 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq271203
    | (have j0 := eq271203 X0 X1 X2
       grind)
    | exact resolve eq271203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271203
  have eq299609 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 (M.op X0 X1))) X2) = (M.op (σ X1) (M.op X2 (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2042 (σ (M.op X0 X0)) (σ X1) X2
       have i₂ := eq2744 X0 X1
       grind)
    | exact superpose eq2744 eq2042
    | exact resolve eq2042 eq2744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042
  have eq299627 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 (M.op X0 X1))) X2) = (M.op X2 (M.op (σ X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3760 X2 (σ X1) (σ (M.op X0 X0))
       have i₂ := eq2744 X0 X1
       grind)
    | exact superpose eq2744 eq3760
    | exact resolve eq3760 eq2744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2744 eq3760
  have eq299656 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq299627 X0 X1 X2
       have i₂ := eq4128 X0 (σ X1) X2
       grind)
    | exact superpose eq4128 eq299627
    | exact resolve eq299627 eq4128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299627
  have eq299674 : ∀ X0 X1 X2 : G, (M.op X2 (σ X1)) = (M.op (σ (M.op X0 (M.op X0 X1))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq299609 X0 X1 X2
       have i₂ := eq4128 X0 X2 (σ X1)
       grind)
    | exact superpose eq4128 eq299609
    | exact resolve eq299609 eq4128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4128 eq299609
  have eq301548 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X0 (M.op X0 X1))) X2) = (M.op X2 (σ (M.op X3 (M.op X1 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq299674 X0 (M.op X3 (M.op X1 X3)) X2
       have i₂ := eq1284 X0 X3 X1
       grind)
    | exact superpose eq1284 eq299674
    | exact resolve eq299674 eq1284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284 eq299674
  have eq302638 : ∀ X1 X2 X3 : G, (M.op (σ X1) X2) = (M.op X2 (σ (M.op X3 (M.op X1 X3)))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq301548 x X1 X2 X3
       have i₂ := eq299656 x X1 X2
       grind)
    | exact superpose eq299656 eq301548
    | exact resolve eq301548 eq299656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299656 eq301548
  have eq304883 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (M.op X2 (τ (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3496 X2 X1 (M.op X1 X0)
       have i₂ := eq2412 X1 X0 X1
       grind)
    | exact superpose eq2412 eq3496
    | exact resolve eq3496 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2412 eq3496
  have eq306790 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (M.op X2 (σ (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3497 X0 X2 (M.op X0 X1)
       have i₂ := eq1287 X0 X0 X1
       grind)
    | exact superpose eq1287 eq3497
    | exact resolve eq3497 eq1287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1287 eq3497
  have eq398408 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2171 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2171
    | exact resolve eq2171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq398505 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq398408 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq398408
    | (have j0 := eq398408 X0 X1
       grind)
    | exact resolve eq398408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398408
  have eq408469 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (σ X0) X1)) = (M.op X2 (M.op X2 (σ (M.op X3 (M.op X0 X3))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2773 X2 (σ (M.op X3 (M.op X0 X3))) X1
       have i₂ := eq302638 X0 X1 X3
       grind)
    | exact superpose eq302638 eq2773
    | exact resolve eq2773 eq302638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773 eq302638
  have eq408559 : ∀ X0 X1 X3 : G, (M.op X1 (M.op (σ X0) X1)) = (σ (M.op X3 (M.op X0 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq408469 X0 X1 x X3
       have i₂ := eq306790 X3 (M.op X0 X3) x
       grind)
    | exact superpose eq306790 eq408469
    | exact resolve eq408469 eq306790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306790 eq408469
  have eq510086 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (τ (M.op X1 X0)) (τ (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq241 (τ (M.op X1 X0)) X2 X2
       have i₂ := eq304883 X0 X1 X2
       grind)
    | exact superpose eq304883 eq241
    | exact resolve eq241 eq304883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq304883
  have eq668020 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq123 X2
       have i₂ := eq510086 X1 X0 (τ X2)
       grind)
    | (have i₁ := eq123 (M.op X0 X0)
       have i₂ := eq510086 X0 X0 X2
       grind)
    | exact superpose eq510086 eq123
    | exact resolve eq123 eq510086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq510086
  have eq685949 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X0 ∨ (σ (k X2 X0)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2797 X1 X2
       have i₂ := eq398505 X0 X2
       grind)
    | (have i₁ := eq2797 X0 X1
       have i₂ := eq398505 (M.op X1 X1) X1
       grind)
    | exact superpose eq398505 eq2797
    | (have j1 := eq398505 X0 X2
       grind)
    | exact resolve eq2797 eq398505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797 eq398505
  have eq948597 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq271219 x y X0
       grind)
    | exact superpose eq271219 eq16
    | (have j1 := eq271219 X0 y X0
       grind)
    | exact resolve eq16 eq271219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271219
  have eq948756 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq948597 X0
       have j1 := eq685949 y X0 x
       grind)
    | (have r₁ := eq948597 X0
       have r₂ := eq685949 y x x
       grind)
    | exact resolve eq948597 eq685949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685949 eq948597
  have eq950942 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq1219 X1 (M.op X1 X0) X0
       have i₂ := eq948756 (M.op X1 X0)
       grind)
    | exact superpose eq948756 eq1219
    | exact resolve eq1219 eq948756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq951626 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X0 X1))) = (M.op (σ X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq408559 X0 (σ X0) X1
       have i₂ := eq948756 (σ X0)
       grind)
    | exact superpose eq948756 eq408559
    | exact resolve eq408559 eq948756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408559
  have eq951759 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq668020 x x X0
       have i₂ := eq948756 (τ (M.op x x))
       grind)
    | exact superpose eq948756 eq668020
    | exact resolve eq668020 eq948756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668020
  have eq951827 : y = (σ y) := by
    first
    | (have i₁ := eq951759 x
       have i₂ := eq948756 x
       grind)
    | exact superpose eq948756 eq951759
    | exact resolve eq951759 eq948756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948756 eq951759
  have eq951951 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X0 X1))) = (M.op y (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq951626 X0 X1
       have i₂ := eq1728 (σ X0) y
       grind)
    | (have i₁ := eq951626 X0 X1
       have i₂ := eq1728 y (σ X0)
       grind)
    | exact superpose eq1728 eq951626
    | exact resolve eq951626 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951626
  have eq954213 : ∀ X0 : G, (σ (M.op X0 y)) = (M.op y (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq951951 X0 x
       have i₂ := eq950942 x X0
       grind)
    | exact superpose eq950942 eq951951
    | exact resolve eq951951 eq950942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950942 eq951951
  have eq957763 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq951827
       grind)
    | exact superpose eq951827 eq16
    | exact resolve eq16 eq951827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951827
  have eq958017 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
    first
    | (have i₁ := eq957763
       have i₂ := eq1728 (σ x) y
       grind)
    | (have i₁ := eq957763
       have i₂ := eq1728 y (σ x)
       grind)
    | exact superpose eq1728 eq957763
    | exact resolve eq957763 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728 eq957763
  have eq958108 : False := by grind
  exact eq958108
