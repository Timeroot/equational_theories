import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1242 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
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
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  clear eq19
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq116 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq546 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq116 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq116
    | exact resolve eq116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq573 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq546
    | (have j0 := eq546 X0 X1
       grind)
    | exact resolve eq546 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq580 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq573 X1 X0
       grind)
    | exact superpose eq573 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq573 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq573 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq573 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq573 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq595 : ∀ X0 X1 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (k X1 X0) = X0 ∨ (σ (k X1 X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq580 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq596 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq595 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq626 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq596 X1 X0
       grind)
    | exact superpose eq596 eq10
    | (have j1 := eq596 X1 X0
       grind)
    | exact resolve eq10 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq662 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq626
    | (have j0 := eq626 X0 X1
       grind)
    | exact resolve eq626 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq684 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq662 (σ X0) X1
       grind)
    | exact superpose eq662 eq37
    | (have j1 := eq662 (σ X0) X1
       grind)
    | exact resolve eq37 eq662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq662
  have eq3341 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq28 (σ X1) X0
       have i₂ := eq684 X1 (σ X0)
       grind)
    | exact superpose eq684 eq28
    | (have j1 := eq684 X1 (σ X0)
       grind)
    | exact resolve eq28 eq684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq684
  have eq3385 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3341 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq3341
    | (have j0 := eq3341 X0 X1
       grind)
    | exact resolve eq3341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341
  have eq3417 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3385 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3385
    | (have j0 := eq3385 X0 X1
       grind)
    | exact resolve eq3385 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3385
  have eq3426 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3417 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3417
    | (have j0 := eq3417 X0 X1
       grind)
    | exact resolve eq3417 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3417
  have eq3476 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq3426 X1 X0
       grind)
    | exact superpose eq3426 eq11
    | (have j1 := eq3426 X1 X0
       grind)
    | exact resolve eq11 eq3426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3426
  have eq4417 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq4842 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3476 x y
       grind)
    | exact superpose eq3476 eq16
    | (have j1 := eq3476 x y
       grind)
    | exact resolve eq16 eq3476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq4881 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4842
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq4842
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq4842
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4842
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4842 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4883 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq4842
       have i₂ := eq596 y x
       grind)
    | exact superpose eq596 eq4842
    | (have j1 := eq596 y x
       grind)
    | (have r₁ := eq4842
       have r₂ := eq596 y x
       grind)
    | (have r₁ := eq4842
       have r₂ := eq596 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq4842
       have r₂ := eq596 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq4842 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596 eq4842
  have eq4884 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4883
  have eq4885 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq4884
  have eq4887 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq4881
  have eq4888 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq4887
  have eq4891 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4885
       grind)
    | exact superpose eq4885 eq16
    | exact resolve eq16 eq4885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4885
  have eq4892 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4891
       have r₂ := eq22 x
       grind)
    | exact resolve eq4891 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4891
  have eq4896 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4417 x y
       have i₂ := eq4892
       grind)
    | exact superpose eq4892 eq4417
    | (have j0 := eq4417 x y
       grind)
    | exact resolve eq4417 eq4892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4417 eq4892
  have eq4901 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq4896
  have eq4902 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq4901
  have eq4906 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4888
       grind)
    | exact superpose eq4888 eq16
    | exact resolve eq16 eq4888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4888
  have eq4907 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq4906
       have r₂ := eq22 x
       grind)
    | exact resolve eq4906 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4906
  have eq4916 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4902
       grind)
    | exact superpose eq4902 eq16
    | exact resolve eq16 eq4902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4902
  have eq4936 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4916
       have i₂ := eq4907
       grind)
    | exact superpose eq4907 eq4916
    | exact resolve eq4916 eq4907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4907 eq4916
  have eq4941 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq4936
  have eq4942 : (σ x) = (σ y) := by grind
  clear eq4941
  have eq4943 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4942
       grind)
    | exact superpose eq4942 eq16
    | exact resolve eq16 eq4942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4944 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4942
       grind)
    | exact superpose eq4942 eq10
    | exact resolve eq10 eq4942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4942
  have eq4995 : x = y := by
    first
    | (have i₁ := eq4944
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4944
    | exact resolve eq4944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4944
  have eq4996 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4943
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq4943
    | exact resolve eq4943 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4943
  have eq4997 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq4996
       have i₂ := eq4995
       grind)
    | exact superpose eq4995 eq4996
    | exact resolve eq4996 eq4995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4995 eq4996
  have eq4998 : False := by grind
  exact eq4998

/-- `Equation1255`: `x = x ◇ (((y ◇ y) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation1255 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1255 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1255.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X1) X2) X1)) = X0 := by
    intro X0 X1 X2
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq20 : ∀ X0 X1 X2 : G, (σ (k X2 (k (τ X0) X1))) = (k (σ X2) (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) X0) ≠ (M.op (M.op (M.op X0 X0) X1) X0) ∨ (k X2 (M.op (M.op (M.op X0 X0) X1) X0)) = (M.op X2 (M.op (M.op (M.op X0 X0) X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op (M.op (M.op X0 X0) X1) X0)
       have i₂ := eq9 (M.op (M.op (M.op X0 X0) X1) X0) X0 X1
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X2 (M.op (M.op (M.op X0 X0) X1) X0)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X1 X1) X2) X1)
       have r₂ := eq9 (M.op (M.op (M.op X1 X1) X2) X1) X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op (M.op X0 X0) X1) X0)) = (M.op X2 (M.op (M.op (M.op X0 X0) X1) X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq36 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op (M.op X0 X0) X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 X0 X1 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq37
    | exact resolve eq37 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq61 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq61
    | (have j0 := eq61 (σ X0) (σ X1)
       grind)
    | exact resolve eq61 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op (M.op X1 X1) X2) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (M.op (M.op (M.op X1 X1) X2) X1)
       have i₂ := eq38 X1 X2 (τ X0)
       grind)
    | exact superpose eq38 eq17
    | exact resolve eq17 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq125 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op (M.op X1 X1) X2) X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq121 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq121
    | exact resolve eq121 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq141 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op (M.op X1 X1) X2) X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 (σ (M.op (M.op (M.op X1 X1) X2) X1))
       have i₂ := eq125 (τ X0) X1 X2
       grind)
    | exact superpose eq125 eq17
    | exact resolve eq17 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op (M.op (M.op X1 X1) X2) X1)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq141 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq141
    | exact resolve eq141 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq246 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (σ X2) (k X0 (σ X1))) ∨ (σ (k X2 (k (τ X0) X1))) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq72 X0 (k (τ X0) X1)
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq72
    | exact resolve eq72 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq72
  have eq947 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (σ X0) = (k (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X0) (k X1 (σ X2))
       have i₂ := eq246 X1 X2 X0
       grind)
    | exact superpose eq246 eq13
    | (have j0 := eq13 (σ X0) (k X1 (σ X2))
       have j1 := eq246 X1 X2 X0
       grind)
    | (have r₁ := eq13 (σ X2) (k X0 (σ X1))
       have r₂ := eq246 X0 X1 X2
       grind)
    | exact resolve eq13 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq948 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (σ X0) = (k (σ X0) (k X1 (σ X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq947 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq949 : ∀ X0 X1 X2 : G, (k X1 (σ X2)) = (M.op (k X1 (σ X2)) (k X1 (σ X2))) ∨ (σ X0) = (σ (k X0 (k (τ X1) X2))) ∨ (σ (k X0 (k (τ X1) X2))) = (M.op (σ X0) (k X1 (σ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq948 X0 X1 X2
       have i₂ := eq20 X1 X2 X0
       grind)
    | exact superpose eq20 eq948
    | (have j0 := eq948 X0 X1 X2
       grind)
    | exact resolve eq948 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq948
  have eq28824 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = X0 ∨ (σ X3) = (σ (k X3 (k (τ X0) (σ (M.op (M.op (M.op X1 X1) X2) X1))))) ∨ (M.op (σ X3) X0) = (σ (k X3 (k (τ X0) (σ (M.op (M.op (M.op X1 X1) X2) X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq949 X0 X0 (σ (M.op (M.op (M.op X1 X1) X2) X1))
       have i₂ := eq148 X0 X1 X2
       grind)
    | exact superpose eq148 eq949
    | (have j0 := eq949 X3 X0 (σ (M.op (M.op (M.op X1 X1) X2) X1))
       grind)
    | exact resolve eq949 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq949
  have eq28920 : ∀ X0 X1 X2 X3 : G, (σ X3) = (σ (k X3 (τ X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ X3) X0) = (σ (k X3 (k (τ X0) (σ (M.op (M.op (M.op X1 X1) X2) X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28824 X0 X1 X2 X3
       have i₂ := eq125 (τ X0) X1 X2
       grind)
    | exact superpose eq125 eq28824
    | (have j0 := eq28824 X0 X1 X2 X3
       grind)
    | exact resolve eq28824 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28824
  have eq28942 : ∀ X0 X1 X2 X3 : G, (σ X3) = (k (σ X3) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ X3) X0) = (σ (k X3 (k (τ X0) (σ (M.op (M.op (M.op X1 X1) X2) X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq28920 X0 X1 X2 X3
       have i₂ := eq18 X0 X3
       grind)
    | exact superpose eq18 eq28920
    | (have j0 := eq28920 X0 X1 X2 X3
       grind)
    | exact resolve eq28920 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28920
  have eq28961 : ∀ X0 X3 : G, (M.op (σ X3) X0) = (σ (k X3 (τ X0))) ∨ (σ X3) = (k (σ X3) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq28942 X0 x x X3
       have i₂ := eq125 (τ X0) x x
       grind)
    | exact superpose eq125 eq28942
    | (have j0 := eq28942 X0 x x X3
       grind)
    | exact resolve eq28942 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq28942
  have eq28980 : ∀ X0 X3 : G, (M.op (σ X3) X0) = (k (σ X3) X0) ∨ (σ X3) = (k (σ X3) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq28961 X0 X3
       have i₂ := eq18 X0 X3
       grind)
    | exact superpose eq18 eq28961
    | (have j0 := eq28961 X0 X3
       grind)
    | exact resolve eq28961 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq28961
  have eq28998 : ∀ X0 X3 : G, (σ X3) = (k (σ X3) X0) ∨ (M.op (σ X3) X0) = (k (σ X3) X0) := by
    intro X0 X3
    first
    | (have j0 := eq28980 X0 X3
       have j1 := eq12 (σ X3) X0
       grind)
    | (have r₁ := eq28980 x X3
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq28980 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28980
  have eq117205 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq28998 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28998
  have eq117220 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq117205 X0 X1
       have j1 := eq61 (σ X0) X1
       grind)
    | (have r₁ := eq117205 X0 X1
       have r₂ := eq61 (σ X0) X1
       grind)
    | exact resolve eq117205 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq117205
  have eq117299 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq117220 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq117220
    | exact resolve eq117220 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117344 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq117220 X0 (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq117220
    | exact resolve eq117220 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117220
  have eq118723 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq117344 X0 X1
       have i₂ := eq117299 X0 X1
       grind)
    | exact superpose eq117299 eq117344
    | exact resolve eq117344 eq117299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117299 eq117344
  have eq118858 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq118723 x y
       grind)
    | exact superpose eq118723 eq16
    | (have r₁ := eq16
       have r₂ := eq118723 x y
       grind)
    | exact resolve eq16 eq118723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118723
  have eq119137 : False := by grind
  exact eq119137

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pyy_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq18
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 X0 (M.op (M.op (M.op X1 X2) X0) X2) X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq284 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op (M.op X2 X3) X0) X3))) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq292 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq297 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq293 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq293 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq293 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq298 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq284 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq284
    | (have j0 := eq284 X0 X1 x x
       grind)
    | exact resolve eq284 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq299 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq298 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq311 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq297 (σ X0)
       grind)
    | exact superpose eq297 eq15
    | exact resolve eq15 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq311 X0
       have i₂ := eq297 X0
       grind)
    | exact superpose eq297 eq311
    | exact resolve eq311 eq297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq311
  have eq406 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op (M.op X2 X3) X0) X3))) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq299 X1 X0
       grind)
    | exact superpose eq299 eq61
    | (have j1 := eq299 (M.op X0 (M.op (M.op (M.op X2 X3) X0) X3)) X1
       grind)
    | exact resolve eq61 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq413 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq299 (σ y) (σ x)
       grind)
    | exact superpose eq299 eq16
    | (have j1 := eq299 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq413
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq413
    | exact resolve eq413 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413
  have eq419 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq406
    | (have j0 := eq406 X0 X1 x x
       grind)
    | exact resolve eq406 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq425 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq419 X1 X0
       grind)
    | exact superpose eq419 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq419 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq419 X0 X1
       grind)
    | exact resolve eq12 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq438 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq587 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq438 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) X2
       have i₂ := eq76 X2 X0 X1
       grind)
    | exact superpose eq76 eq9
    | exact resolve eq9 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq917 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1 x (M.op X0 X1)
       have i₂ := eq862 x (M.op X0 X1) X0
       grind)
    | exact superpose eq862 eq61
    | exact resolve eq61 eq862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq862
  have eq940 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq917 X0 (M.op X1 X0)
       have i₂ := eq917 X1 X0
       grind)
    | exact superpose eq917 eq917
    | exact resolve eq917 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq917 (σ X0) (σ X0)
       have i₂ := eq330 X0
       grind)
    | exact superpose eq330 eq917
    | exact resolve eq917 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq947 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 (M.op X2 X0)
       have i₂ := eq917 X2 X0
       grind)
    | exact superpose eq917 eq9
    | exact resolve eq9 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X0) X0
       have i₂ := eq917 X1 X0
       grind)
    | exact superpose eq917 eq12
    | (have j0 := eq12 (M.op X1 X0) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X1
       have r₂ := eq917 X0 X1
       grind)
    | exact resolve eq12 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have j0 := eq948 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1002 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq940 X1 X0
       grind)
    | exact superpose eq940 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X0)
       have r₂ := eq940 X0 X1
       grind)
    | exact resolve eq12 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (k X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1002 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1017 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1014 X0 X1
       have i₂ := eq917 X0 X1
       grind)
    | exact superpose eq917 eq1014
    | exact resolve eq1014 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq1026 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1017 X0 X1
       have i₂ := eq419 X1 X0
       grind)
    | exact superpose eq419 eq1017
    | (have j1 := eq419 X1 X0
       grind)
    | exact resolve eq1017 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1027 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1017 X0 X1
       have i₂ := eq299 X1 X0
       grind)
    | exact superpose eq299 eq1017
    | (have j1 := eq299 X1 X0
       grind)
    | exact resolve eq1017 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1045 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 (σ X0))
       have i₂ := eq1017 X1 (σ X0)
       grind)
    | exact superpose eq1017 eq28
    | exact resolve eq28 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1017
  have eq1052 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1045 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1045
    | exact resolve eq1045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1182 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1052 X1 X0
       have i₂ := eq419 (σ X1) X0
       grind)
    | exact superpose eq419 eq1052
    | (have j1 := eq419 (σ X1) X0
       grind)
    | exact resolve eq1052 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1183 : ∀ X0 X1 : G, (k X1 (τ X0)) = X1 ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1052 X1 X0
       have i₂ := eq299 (σ X1) X0
       grind)
    | exact superpose eq299 eq1052
    | (have j1 := eq299 (σ X1) X0
       grind)
    | exact resolve eq1052 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299 eq1052
  have eq1231 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) X1) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq945 X0
       grind)
    | exact superpose eq945 eq9
    | exact resolve eq9 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq1969 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1026 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2058 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1027 (τ X1) X0
       grind)
    | exact superpose eq1027 eq17
    | (have j1 := eq1027 (τ X1) X0
       grind)
    | exact resolve eq17 eq1027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1027
  have eq9166 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1182 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1182
    | (have j0 := eq1182 (σ X0) X1
       grind)
    | exact resolve eq1182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq9224 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9166 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9166
    | (have j0 := eq9166 X0 X1
       grind)
    | exact resolve eq9166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9166
  have eq9483 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1183 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1183
    | (have j0 := eq1183 (σ X0) X1
       grind)
    | exact resolve eq1183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183
  have eq9544 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9483 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq9483
    | (have j0 := eq9483 X0 X1
       grind)
    | exact resolve eq9483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9483
  have eq12100 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9224 x y
       grind)
    | exact superpose eq9224 eq16
    | (have j1 := eq9224 x y
       grind)
    | exact resolve eq16 eq9224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9224
  have eq12432 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12100
       have i₂ := eq1026 x y
       grind)
    | exact superpose eq1026 eq12100
    | (have j1 := eq1026 x y
       grind)
    | exact resolve eq12100 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026 eq12100
  have eq12437 : y = (M.op x y) ∨ y = (k y x) := by grind
  clear eq12432
  have eq12443 : y = (k y x) := by
    first
    | (have j1 := eq1969 y x
       grind)
    | (have r₁ := eq12437
       have r₂ := eq1969 y x
       grind)
    | exact resolve eq12437 eq1969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1969 eq12437
  have eq12459 : y = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq438 x y
       have i₂ := eq12443
       grind)
    | exact superpose eq12443 eq438
    | exact resolve eq438 eq12443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12520 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq917 y x
       have i₂ := eq12459
       grind)
    | exact superpose eq12459 eq917
    | exact resolve eq917 eq12459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12459
  have eq12615 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y (M.op y (M.op X0 x))) := by
    intro X0
    first
    | (have i₁ := eq947 x y X0
       have i₂ := eq12520
       grind)
    | exact superpose eq12520 eq947
    | exact resolve eq947 eq12520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq14248 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 x))) ∨ (M.op x y) = (k x y) := by
    intro X0
    first
    | (have i₁ := eq967 y x
       have i₂ := eq12615 X0
       grind)
    | exact superpose eq12615 eq967
    | (have j1 := eq12615 X0
       grind)
    | exact resolve eq967 eq12615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq12615
  have eq15200 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9544 y x
       grind)
    | exact superpose eq9544 eq16
    | (have j1 := eq9544 y x
       grind)
    | exact resolve eq16 eq9544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9544
  have eq15374 : (σ (M.op x y)) ≠ (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq15200
       have i₂ := eq12443
       grind)
    | exact superpose eq12443 eq15200
    | exact resolve eq15200 eq12443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15200
  have eq15444 : (σ y) ≠ (σ y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15374
       have i₂ := eq12520
       grind)
    | exact superpose eq12520 eq15374
    | exact resolve eq15374 eq12520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12520
  have eq15456 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq15444
  have eq15479 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq438 y x
       have i₂ := eq15456
       grind)
    | exact superpose eq15456 eq438
    | exact resolve eq438 eq15456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq15456
  have eq15487 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq15479
  have eq25144 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2058 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2058
    | exact resolve eq2058 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2058
  have eq25235 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25144 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq25144
    | (have j0 := eq25144 X0 X1
       grind)
    | exact resolve eq25144 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25144
  have eq25354 : (σ (M.op x y)) = (σ y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq25235 y x
       have i₂ := eq12443
       grind)
    | exact superpose eq12443 eq25235
    | (have j0 := eq25235 y x
       grind)
    | exact resolve eq25235 eq12443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25235
  have eq25470 : x = (k x y) := by
    first
    | (have r₁ := eq25354
       have r₂ := eq15374
       grind)
    | exact resolve eq25354 eq15374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15374 eq25354
  have eq46823 : y = (M.op y (M.op y x)) ∨ (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq14248 y
       have i₂ := eq15487
       grind)
    | exact superpose eq15487 eq14248
    | exact resolve eq14248 eq15487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14248
  have eq46976 : x = (M.op x y) ∨ y = (M.op y (M.op y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46823
       have i₂ := eq25470
       grind)
    | exact superpose eq25470 eq46823
    | exact resolve eq46823 eq25470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46823
  have eq46977 : y = (M.op y (M.op y x)) ∨ x = (M.op x y) := by grind
  clear eq46976
  have eq47007 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46977
       have i₂ := eq15487
       grind)
    | exact superpose eq15487 eq46977
    | exact resolve eq46977 eq15487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15487 eq46977
  have eq47093 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq47007
  have eq47157 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq917 y x
       have i₂ := eq47093
       grind)
    | exact superpose eq47093 eq917
    | exact resolve eq917 eq47093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917 eq47093
  have eq47200 : x = (M.op x y) := by grind
  clear eq47157
  have eq94759 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) := by
    first
    | (have i₁ := eq418
       have i₂ := eq47200
       grind)
    | exact superpose eq47200 eq418
    | exact resolve eq418 eq47200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq94772 : (M.op (σ y) (σ x)) = (σ (k x y)) := by grind
  clear eq94759
  have eq94798 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq94772
       have i₂ := eq25470
       grind)
    | exact superpose eq25470 eq94772
    | exact resolve eq94772 eq25470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25470 eq94772
  have eq94881 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq587 (σ y) (σ x)
       have i₂ := eq94798
       grind)
    | exact superpose eq94798 eq587
    | (have j0 := eq587 (σ y) (σ x)
       grind)
    | exact resolve eq587 eq94798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq94891 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq940 (σ x) (σ y)
       have i₂ := eq94798
       grind)
    | exact superpose eq94798 eq940
    | exact resolve eq940 eq94798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq94971 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq94891
       have i₂ := eq330 x
       grind)
    | exact superpose eq330 eq94891
    | exact resolve eq94891 eq330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330 eq94891
  have eq94975 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have j1 := eq419 (σ y) (σ x)
       grind)
    | (have r₁ := eq94881
       have r₂ := eq419 (σ y) (σ x)
       grind)
    | exact resolve eq94881 eq419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq94881
  have eq95012 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq94975
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq94975
    | exact resolve eq94975 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94975
  have eq95031 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq95012
       have i₂ := eq12443
       grind)
    | exact superpose eq12443 eq95012
    | exact resolve eq95012 eq12443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12443 eq95012
  have eq95627 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95031
       grind)
    | exact superpose eq95031 eq16
    | exact resolve eq16 eq95031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95637 : (σ y) = (M.op (σ y) (M.op (σ y) (σ (M.op x x)))) := by
    first
    | (have i₁ := eq1231 x (σ y)
       have i₂ := eq95031
       grind)
    | exact superpose eq95031 eq1231
    | exact resolve eq1231 eq95031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1231 eq95031
  have eq95787 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq95637
       have i₂ := eq94971
       grind)
    | exact superpose eq94971 eq95637
    | exact resolve eq95637 eq94971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94971 eq95637
  have eq95791 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq95627
       have i₂ := eq47200
       grind)
    | exact superpose eq47200 eq95627
    | exact resolve eq95627 eq47200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47200 eq95627
  have eq95818 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq95787
       have i₂ := eq94798
       grind)
    | exact superpose eq94798 eq95787
    | exact resolve eq95787 eq94798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95787
  have eq95830 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq95818
       have i₂ := eq94798
       grind)
    | exact superpose eq94798 eq95818
    | exact resolve eq95818 eq94798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94798 eq95818
  have eq95840 : False := by grind
  exact eq95840

/-- `Equation1265`: `x = x ◇ (((y ◇ z) ◇ y) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyx_pxy_Equation1265 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1265 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1265.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X5 : G, (M.op X1 (M.op (M.op X0 X0) X5)) = X1 := by
    intro X0 X1 X5
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op (M.op x x) x) x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
       have i₂ := eq14 (M.op (M.op X0 X1) X0) x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq73
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq73
    | exact resolve eq73 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq80
    | exact resolve eq80 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq82
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq82
    | exact resolve eq82 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq90 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq92 : (σ (k y (M.op x y))) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq100 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq16
    | exact resolve eq16 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = X0 := by
    intro X0
    first
    | (have i₁ := eq57 X0 (M.op (M.op (M.op x x) x) x)
       have i₂ := eq14 (M.op sF4 sF2) x x x
       grind)
    | exact superpose eq14 eq57
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq240 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1 (M.op (M.op x x) x)
       have i₂ := eq58 x (M.op X0 X0) x
       grind)
    | exact superpose eq58 eq58
    | exact resolve eq58 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq297 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X1 X1) X0
       have i₂ := eq240 X1 X0
       grind)
    | exact superpose eq240 eq13
    | (have j0 := eq13 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq240 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq68 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq68 X0 X1
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq488 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq489 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq488 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488
  have eq492 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq482 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq494 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq492 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq492 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq492 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq492 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq498 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq494 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq494
    | (have j0 := eq494 X0 X1
       grind)
    | exact resolve eq494 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq2128 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq297 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq5600 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq83 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq5601 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq5600
    | exact resolve eq5600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5600
  have eq5612 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq5601
       have r₂ := eq27
       grind)
    | exact resolve eq5601 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5601
  have eq5614 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq5612
    | exact resolve eq5612 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5612
  have eq5617 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq5614 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq5614
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq5614
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5614
       grind)
    | exact resolve eq13 eq5614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5614
  have eq5625 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq5617
  have eq5645 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq5625 eq55
    | exact resolve eq55 eq5625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq5625
  have eq5664 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq5645
    | exact resolve eq5645 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5645
  have eq5667 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq5664
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq5664
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq5664
       have r₂ := eq13 x y
       grind)
    | exact resolve eq5664 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5664
  have eq5669 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq5667
       grind)
    | exact superpose eq5667 eq44
    | exact resolve eq44 eq5667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq5676 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq5667
       grind)
    | exact superpose eq5667 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq5667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667
  have eq5677 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5676
  have eq5679 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5677
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5677
    | exact resolve eq5677 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5677
  have eq5680 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5679
  have eq5687 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5669
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5669
    | exact resolve eq5669 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5669
  have eq5690 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq5680
       grind)
    | exact superpose eq5680 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq5680
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq5680
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq5680
       grind)
    | exact resolve eq12 eq5680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5680
  have eq5700 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5690
  have eq5708 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5700
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5700
    | exact resolve eq5700 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5700
  have eq5709 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5708
  have eq5713 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5709
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5709
    | exact resolve eq5709 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5709
  have eq5727 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5687 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq5687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5687
  have eq5728 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5727
  have eq5732 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5728
    | exact resolve eq5728 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5728
  have eq5733 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5732
  have eq5798 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq5713
       grind)
    | exact superpose eq5713 eq90
    | exact resolve eq90 eq5713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5713
  have eq5812 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq5798
    | exact resolve eq5798 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5798
  have eq5813 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5733 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq5733
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq5733
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq5733
       grind)
    | exact resolve eq12 eq5733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5733
  have eq5823 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5813
  have eq5831 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5823
    | exact resolve eq5823 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5823
  have eq5832 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq5831
  have eq5836 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5832
    | exact resolve eq5832 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5832
  have eq6106 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5836 eq5812
    | exact resolve eq5812 eq5836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5812 eq5836
  have eq6108 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6106
  have eq6110 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6108
       have r₂ := eq27
       grind)
    | exact resolve eq6108 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6108
  have eq6113 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6110 eq51
    | (have r₁ := eq51
       have r₂ := eq6110
       grind)
    | exact resolve eq51 eq6110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq6110
  have eq6123 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq6113
  have eq6311 : (τ (σ x)) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6123 eq100
    | exact resolve eq100 eq6123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq6123
  have eq6334 : x = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq6311
    | exact resolve eq6311 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq6311
  have eq6336 : x = (k y x) := by
    first
    | (have r₁ := eq6334
       have r₂ := eq50
       grind)
    | exact resolve eq6334 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq6334
  have eq6508 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq6336
       grind)
    | exact superpose eq6336 eq90
    | exact resolve eq90 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6516 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq6336
       grind)
    | exact superpose eq6336 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6517 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq6516
  have eq6519 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6517
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6517
    | exact resolve eq6517 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6517
  have eq6526 : (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq6508
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6508
    | exact resolve eq6508 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6508
  have eq6540 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6526 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq6526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6541 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq6540
  have eq6543 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq6541
    | exact resolve eq6541 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6541
  have eq6553 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq6519
       grind)
    | exact superpose eq6519 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq6519
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq6519
       grind)
    | exact resolve eq12 eq6519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6557 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq60 y x X0
       have i₂ := eq6519
       grind)
    | exact superpose eq6519 eq60
    | exact resolve eq60 eq6519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6519
  have eq6564 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq6553
  have eq6570 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq6557 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6557
    | (have j0 := eq6557 X0
       grind)
    | exact resolve eq6557 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6557
  have eq6573 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6564
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6564
    | exact resolve eq6564 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6564
  have eq6574 : y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq6573
  have eq6578 : x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6574
       have i₂ := eq6336
       grind)
    | exact superpose eq6336 eq6574
    | exact resolve eq6574 eq6336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6336 eq6574
  have eq6580 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6578
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6578
    | exact resolve eq6578 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq6578
  have eq6761 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6580 eq20
    | exact resolve eq20 eq6580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6580
  have eq6873 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6761
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6761
    | exact resolve eq6761 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6761
  have eq6888 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6873 eq26
    | exact resolve eq26 eq6873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7005 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6873 eq6543
    | exact resolve eq6543 eq6873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7006 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6543 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq6543
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq6543
       grind)
    | exact resolve eq12 eq6543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6543
  have eq7017 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7006
  have eq7026 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq7017
    | exact resolve eq7017 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7017
  have eq7027 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq7026
  have eq7028 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7005
       have r₂ := eq27
       grind)
    | exact resolve eq7005 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005
  have eq7032 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6526 eq7027
    | exact resolve eq7027 eq6526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7027
  have eq7034 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq7032
    | exact resolve eq7032 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7032
  have eq7035 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7034 eq27
    | exact resolve eq27 eq7034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7034
  have eq7049 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6873 eq7035
    | (have r₁ := eq7035
       have r₂ := eq6873
       grind)
    | exact resolve eq7035 eq6873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6873 eq7035
  have eq7050 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7049
  have eq7054 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7050 eq27
    | exact resolve eq27 eq7050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7468 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6570 eq2128
    | exact resolve eq2128 eq6570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2128 eq6570
  have eq7871 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7468 eq489
    | (have j0 := eq489 (M.op x y)
       grind)
    | exact resolve eq489 eq7468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq7468
  have eq7874 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by grind
  clear eq7871
  have eq7877 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq7874
    | exact resolve eq7874 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7874
  have eq7922 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ (M.op x y)))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7028 eq60
    | exact resolve eq60 eq7028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq8147 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7877 eq240
    | exact resolve eq240 eq7877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq7877
  have eq12306 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6888 eq7922
    | exact resolve eq7922 eq6888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6888 eq7922
  have eq12405 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12306 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12306
  have eq12547 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7050 eq12405
    | exact resolve eq12405 eq7050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7050 eq12405
  have eq12651 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12547 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12547
  have eq12775 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12651 eq7028
    | exact resolve eq7028 eq12651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7028 eq12651
  have eq12790 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq12775
  have eq12792 : x = (M.op x y) := by
    first
    | (have r₁ := eq12790
       have r₂ := eq7054
       grind)
    | exact resolve eq12790 eq7054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7054 eq12790
  have eq12962 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq12792 eq20
    | exact resolve eq20 eq12792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12968 : (σ (k y x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq12792 eq92
    | exact resolve eq92 eq12792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13072 : (k (σ y) (σ x)) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq12968
       have i₂ := eq90
       grind)
    | exact superpose eq90 eq12968
    | exact resolve eq12968 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq12968
  have eq13076 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12962
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12962
    | exact resolve eq12962 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12962
  have eq13085 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq6526 eq13072
    | exact resolve eq13072 eq6526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526 eq13072
  have eq13089 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13076 eq26
    | exact resolve eq26 eq13076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13237 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq13076 eq13085
    | exact resolve eq13085 eq13076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13085
  have eq13572 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq92 eq498
    | (have j0 := eq498 y (M.op x y)
       grind)
    | exact resolve eq498 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq498
  have eq13639 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13237 eq13572
    | (have r₁ := eq13572
       have r₂ := eq13237
       grind)
    | exact resolve eq13572 eq13237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13572
  have eq13748 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq13639
       have r₂ := eq20
       grind)
    | exact resolve eq13639 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13639
  have eq13853 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq13748
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13748
    | exact resolve eq13748 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13748
  have eq13948 : (k (σ y) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq13853
    | exact resolve eq13853 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13853
  have eq14035 : (M.op (σ x) (σ y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13089 eq13948
    | exact resolve eq13948 eq13089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13948
  have eq14115 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq13237 eq14035
    | exact resolve eq14035 eq13237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13237 eq14035
  have eq14179 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have r₁ := eq14115
       have r₂ := eq27
       grind)
    | exact resolve eq14115 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14115
  have eq14241 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq14179
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14179
    | exact resolve eq14179 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14179
  have eq14297 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq14241
    | exact resolve eq14241 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq14241
  have eq14328 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13089 eq14297
    | exact resolve eq14297 eq13089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13089 eq14297
  have eq14382 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq14328 eq27
    | exact resolve eq27 eq14328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq14386 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq14328 eq225
    | exact resolve eq225 eq14328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq14405 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ (M.op x y)))) = X0 := by
    intro X0
    first
    | exact superpose eq13076 eq14386
    | exact resolve eq14386 eq13076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14386
  have eq15764 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8147 eq14405
    | exact resolve eq14405 eq8147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8147 eq14405
  have eq15887 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq12792 eq15764
    | (have j0 := eq15764 X0
       grind)
    | exact resolve eq15764 eq12792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12792 eq15764
  have eq16293 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq15887 eq26
    | (have j1 := eq15887 (σ x)
       grind)
    | exact resolve eq26 eq15887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15887
  have eq16295 : (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq14328 eq16293
    | exact resolve eq16293 eq14328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14328 eq16293
  have eq16313 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq13076 eq16295
    | exact resolve eq16295 eq13076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16295
  have eq16323 : x = y := by
    first
    | (have r₁ := eq16313
       have r₂ := eq14382
       grind)
    | exact resolve eq16313 eq14382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16313
  have eq17721 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq16323
       grind)
    | exact superpose eq16323 eq24
    | exact resolve eq24 eq16323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16323
  have eq17837 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq17721
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17721
    | exact resolve eq17721 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17721
  have eq17888 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq13076 eq17837
    | exact resolve eq17837 eq13076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13076 eq17837
  have eq17919 : False := by grind
  exact eq17919

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq277 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq84 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq84 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq84 X0 X1
       grind)
    | exact resolve eq13 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq280 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq281 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq282 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq284 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq282 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq282
    | (have j0 := eq282 X0 X1
       grind)
    | exact resolve eq282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq288 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq284 X0 X1
       have j1 := eq280 X0 X1
       grind)
    | (have r₁ := eq284 X0 X1
       have r₂ := eq280 X0 X1
       grind)
    | (have r₁ := eq284 X0 (k X1 X0)
       have r₂ := eq280 X0 X1
       grind)
    | (have r₁ := eq284 X0 X0
       have r₂ := eq280 X0 X0
       grind)
    | exact resolve eq284 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280 eq284
  have eq520 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq288 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq288
    | exact resolve eq288 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq288 x y
       grind)
    | exact superpose eq288 eq16
    | (have j1 := eq288 x y
       grind)
    | exact resolve eq16 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq551 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq520 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq520
    | (have j0 := eq520 X0 X1
       grind)
    | exact resolve eq520 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq520
  have eq556 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq551
    | exact resolve eq551 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq621 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq556 (τ X1) X0
       grind)
    | exact superpose eq556 eq18
    | (have j1 := eq556 (τ X1) X0
       grind)
    | exact resolve eq18 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq556
  have eq809 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq621 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq621
    | exact resolve eq621 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq857 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq809 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq809
    | (have j0 := eq809 X0 X1
       grind)
    | exact resolve eq809 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq955 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq534
       have i₂ := eq857 y x
       grind)
    | exact superpose eq857 eq534
    | (have j1 := eq857 (σ y) (σ x)
       grind)
    | (have r₁ := eq534
       have r₂ := eq857 y x
       grind)
    | exact resolve eq534 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq955
  have eq964 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq956
  have eq973 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq534
       have i₂ := eq964
       grind)
    | exact superpose eq964 eq534
    | exact resolve eq534 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534 eq964
  have eq974 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq973
  have eq975 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq974
  have eq1027 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq975
  have eq1037 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1027
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1027
    | exact resolve eq1027 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq1043 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1037
       grind)
    | exact superpose eq1037 eq16
    | exact resolve eq16 eq1037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1037
  have eq1090 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1043
       have i₂ := eq857 y x
       grind)
    | exact superpose eq857 eq1043
    | (have j1 := eq857 y x
       grind)
    | (have r₁ := eq1043
       have r₂ := eq857 y x
       grind)
    | exact resolve eq1043 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq1091 : y = (M.op x x) := by grind
  clear eq1090
  have eq1097 : (M.op x y) = (k y x) := by grind
  clear eq1091
  have eq1138 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1043
       have i₂ := eq1097
       grind)
    | exact superpose eq1097 eq1043
    | exact resolve eq1043 eq1097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1043 eq1097
  have eq1141 : False := by grind
  exact eq1141

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_y_pxy_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq348 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq446 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq348 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq348
    | exact resolve eq348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq458 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq348 X0 X1
       grind)
    | exact superpose eq348 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq348 X0 (σ X0)
       grind)
    | (have r₁ := eq13 X1 (σ X0)
       have r₂ := eq348 X0 X1
       grind)
    | exact resolve eq13 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq463 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq458 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq469 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq463 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq463 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq463 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463
  have eq500 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq469 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq469
    | exact resolve eq469 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq562 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq500 X1 (τ X0)
       grind)
    | exact superpose eq500 eq17
    | (have j1 := eq500 X1 (τ X0)
       grind)
    | exact resolve eq17 eq500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq568 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq500 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq967 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq562 X1 (τ X0)
       grind)
    | exact superpose eq562 eq18
    | (have j1 := eq562 X1 (τ X0)
       grind)
    | exact resolve eq18 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq562
  have eq976 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq967 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq967
    | (have j0 := eq967 X0 X1
       grind)
    | exact resolve eq967 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967
  have eq987 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq976 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq976
    | (have j0 := eq976 X0 X1
       grind)
    | exact resolve eq976 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq988 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq987 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq987
    | (have j0 := eq987 X0 X1
       grind)
    | exact resolve eq987 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq987
  have eq1045 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq988 X0 X1
       have i₂ := eq446 X0 X1
       grind)
    | exact superpose eq446 eq988
    | (have j1 := eq446 X1 X0
       grind)
    | exact resolve eq988 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1084 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq1045 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1242 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq568 X1 X0
       have i₂ := eq1084 X1 X0
       grind)
    | exact superpose eq1084 eq568
    | (have j0 := eq568 X1 X0
       have j1 := eq1084 X1 X0
       grind)
    | (have r₁ := eq568 X0 X1
       have r₂ := eq1084 X0 X1
       grind)
    | exact resolve eq568 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq1255 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) (τ (σ y)))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1084 (σ x) (σ y)
       grind)
    | exact superpose eq1084 eq16
    | (have j1 := eq1084 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq1084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1267 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq1242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1280 : (M.op (σ x) (σ y)) = (σ (M.op (τ (σ x)) y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1255
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq1255
    | exact resolve eq1255 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1302 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq1280
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1280
    | exact resolve eq1280 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1280
  have eq1308 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq1302
       have r₂ := eq16
       grind)
    | exact resolve eq1302 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1520 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq1267 (σ X0) X1
       grind)
    | exact superpose eq1267 eq22
    | (have j1 := eq1267 (σ X0) X1
       grind)
    | exact resolve eq22 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1267
  have eq1559 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1520 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1520
    | (have j0 := eq1520 X0 X1
       grind)
    | exact resolve eq1520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520
  have eq1576 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1559 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1559
    | (have j0 := eq1559 X0 X1
       grind)
    | exact resolve eq1559 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq2727 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1576 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1576
    | exact resolve eq1576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1576
  have eq2829 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2727 x y
       grind)
    | exact superpose eq2727 eq16
    | (have j1 := eq2727 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq2727 x y
       grind)
    | exact resolve eq16 eq2727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2727
  have eq2853 : y = (k x y) := by grind
  clear eq2829
  have eq2923 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq446 y x
       have i₂ := eq2853
       grind)
    | exact superpose eq2853 eq446
    | (have j0 := eq446 y x
       grind)
    | exact resolve eq446 eq2853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq2853
  have eq2926 : y = (M.op x y) := by grind
  clear eq2923
  have eq2931 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1308
       have i₂ := eq2926
       grind)
    | exact superpose eq2926 eq1308
    | exact resolve eq1308 eq2926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308 eq2926
  have eq2939 : False := by grind
  exact eq2939

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation1434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
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
  have eq97 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq97 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq97 X0 X1
       grind)
    | exact superpose eq97 eq13
    | (have j0 := eq13 (k (σ X1) (σ X0)) (M.op (σ X0) (σ X1))
       have j1 := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq97 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq97 X0 X1
       grind)
    | exact resolve eq13 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq264 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq265 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq272 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq265 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq265
    | (have j0 := eq265 X0 X1
       grind)
    | exact resolve eq265 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq273 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq388 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq273 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq273
    | exact resolve eq273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq273 x y
       grind)
    | exact superpose eq273 eq16
    | (have j1 := eq273 x y
       grind)
    | exact resolve eq16 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq414 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq388
    | (have j0 := eq388 X0 X1
       grind)
    | exact resolve eq388 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq388
  have eq440 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq414 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq414
    | exact resolve eq414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq538 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq394
       have i₂ := eq440 x y
       grind)
    | exact superpose eq440 eq394
    | (have j1 := eq440 (σ x) (σ y)
       grind)
    | (have r₁ := eq394
       have r₂ := eq440 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq394
       have r₂ := eq440 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq394 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394 eq440
  have eq541 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq538
  have eq588 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq541
       grind)
    | exact superpose eq541 eq10
    | exact resolve eq10 eq541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq623 : x = y ∨ x = y := by
    first
    | (have i₁ := eq588
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq588
    | exact resolve eq588 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq624 : x = y := by grind
  clear eq623
  have eq626 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq624
       grind)
    | exact superpose eq624 eq16
    | exact resolve eq16 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq627 : False := by grind
  exact eq627

/-- `Equation1437`: `x = (x ◇ x) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_x_pyx_Equation1437 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1437.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op X2 X0)) X3 (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X0 X0) x
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq271 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq271
    | (have j0 := eq271 (σ X0) (σ X1)
       grind)
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq271 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq271
    | (have j0 := eq271 (τ X0) (τ X1)
       grind)
    | exact resolve eq271 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq271 X1 (σ X0)
       grind)
    | exact superpose eq271 eq22
    | (have j1 := eq271 X1 (σ X0)
       grind)
    | exact resolve eq22 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq283 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq271 X1 (τ X0)
       grind)
    | exact superpose eq271 eq18
    | (have j1 := eq271 X1 (τ X0)
       grind)
    | exact resolve eq18 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq287 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq271 (σ X1) X0
       grind)
    | exact superpose eq271 eq28
    | (have j1 := eq271 (σ X1) X0
       grind)
    | exact resolve eq28 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq354 : ∀ X0 X1 X2 : G, (τ (k X2 (k (σ X0) X1))) = (k (τ X2) (M.op (τ X1) X0)) ∨ (τ X1) = (M.op (τ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X2 (M.op (τ X1) X0)
       have i₂ := eq283 X1 X0
       grind)
    | exact superpose eq283 eq22
    | (have j1 := eq283 X1 X0
       grind)
    | exact resolve eq22 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq406 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq272 X1 X0
       have i₂ := eq271 X1 X0
       grind)
    | exact superpose eq271 eq272
    | (have j0 := eq272 X1 X0
       have j1 := eq271 (σ X1) (σ X0)
       grind)
    | exact resolve eq272 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq272 X1 X0
       grind)
    | exact superpose eq272 eq10
    | (have j1 := eq272 X1 X0
       grind)
    | exact resolve eq10 eq272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq542 : ∀ X0 X1 X2 : G, (τ X0) = (M.op (τ (k X0 X0)) (M.op X1 (M.op X2 (τ X0)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (τ X0) X1 X2
       have i₂ := eq273 X0 X0
       grind)
    | exact superpose eq273 eq9
    | (have j1 := eq273 X0 X0
       grind)
    | exact resolve eq9 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (k (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq273 X0 X1
       grind)
    | exact superpose eq273 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq273 X1 X0
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq273 X0 X1
       grind)
    | exact resolve eq13 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq273 X0 X1
       grind)
    | exact superpose eq273 eq12
    | (have j0 := eq12 (τ X1) (τ X0)
       have j1 := eq273 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) (τ X0)
       have r₂ := eq273 X0 X1
       grind)
    | exact resolve eq12 eq273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq273 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq548 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq545 X0 X1
       have j1 := eq12 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq545 X0 X1
       have r₂ := eq12 (τ X1) (τ X0)
       grind)
    | exact resolve eq545 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq549 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (k (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq543 X0 X1
       have j1 := eq13 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq543 X0 X1
       have r₂ := eq13 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq543 X0 X1
       have r₂ := eq13 (τ X0) (τ X1)
       grind)
    | exact resolve eq543 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq554 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq548
    | (have j0 := eq548 X0 X1
       grind)
    | exact resolve eq548 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq555 : ∀ X0 X1 : G, (τ X1) ≠ (τ (k X0 X1)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq549 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq549
    | (have j0 := eq549 X0 X1
       grind)
    | exact resolve eq549 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq549
  have eq557 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq547 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq547
    | (have j0 := eq547 (σ X1) (σ X0)
       grind)
    | exact resolve eq547 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq557 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq557
    | (have j0 := eq557 X0 X1
       grind)
    | exact resolve eq557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq569 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq567
    | (have j0 := eq567 X0 X1
       grind)
    | exact resolve eq567 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq570 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq569 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq569
    | (have j0 := eq569 X0 X1
       grind)
    | exact resolve eq569 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq571 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq570 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq570
    | (have j0 := eq570 X0 X1
       grind)
    | exact resolve eq570 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq573 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq571 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq571
    | (have j0 := eq571 (σ X0) (σ X1)
       grind)
    | exact resolve eq571 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq554 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq554
    | (have j0 := eq554 (σ X0) (σ X1)
       grind)
    | exact resolve eq554 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq640 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq625
    | (have j0 := eq625 X0 X1
       grind)
    | exact resolve eq625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq643 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq640 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq640
    | (have j0 := eq640 X0 X1
       grind)
    | exact resolve eq640 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq645 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (τ (k (σ X1) (σ X0))) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq643 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq643
    | (have j0 := eq643 X0 X1
       grind)
    | exact resolve eq643 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq646 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (k (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq645 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq645
    | (have j0 := eq645 X0 X1
       grind)
    | exact resolve eq645 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq645
  have eq647 : ∀ X0 X1 : G, (k X1 X0) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq646 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq646
    | (have j0 := eq646 X0 X1
       grind)
    | exact resolve eq646 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq648 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq647
    | (have j0 := eq647 X0 X1
       grind)
    | exact resolve eq647 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq650 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq648 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq648
    | (have j0 := eq648 (σ X0) (σ X1)
       grind)
    | exact resolve eq648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq650 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq650
    | (have j0 := eq650 X0 X1
       grind)
    | exact resolve eq650 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq3233 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X4 (M.op X2 (M.op X3 X0)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op X1 (M.op X2 X0)) X1 (M.op X0 X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4764 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq406 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq406
    | (have j0 := eq406 X0 (σ X1)
       grind)
    | exact resolve eq406 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4784 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq406 x y
       grind)
    | exact superpose eq406 eq16
    | (have j1 := eq406 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq406 x y
       grind)
    | exact resolve eq16 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4797 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X1) (σ X0)
       have i₂ := eq406 X0 X1
       grind)
    | exact superpose eq406 eq62
    | (have j1 := eq406 X0 X1
       grind)
    | exact resolve eq62 eq406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq4804 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4784
  have eq4821 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4804
       grind)
    | exact superpose eq4804 eq16
    | exact resolve eq16 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4822 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) X0 (σ x)
       have i₂ := eq4804
       grind)
    | exact superpose eq4804 eq9
    | exact resolve eq9 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4823 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq4804
       grind)
    | exact superpose eq4804 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4804
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4804
       grind)
    | exact resolve eq12 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4824 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq4804
       grind)
    | exact superpose eq4804 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq4804
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4804
       grind)
    | exact resolve eq13 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4825 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) (M.op X1 (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ y) X1 (σ x) x
       have i₂ := eq4804
       grind)
    | exact superpose eq4804 eq61
    | exact resolve eq61 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4827 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62 (σ y) (σ x)
       have i₂ := eq4804
       grind)
    | exact superpose eq4804 eq62
    | exact resolve eq62 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4828 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op X0 (M.op X1 (M.op X2 (σ y))))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3233 (σ y) (σ x) X2 x x
       have i₂ := eq4804
       grind)
    | exact superpose eq4804 eq3233
    | exact resolve eq3233 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4829 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) (M.op X1 (M.op X2 (σ x)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3233 (σ y) X0 X2 (σ x) X1
       have i₂ := eq4804
       grind)
    | exact superpose eq4804 eq3233
    | exact resolve eq3233 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4831 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4824
  have eq4832 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4823
  have eq4834 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4831
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq4831
    | exact resolve eq4831 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4831
  have eq4835 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4832
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4832
    | exact resolve eq4832 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4832
  have eq4837 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq271 eq4834
    | (have j1 := eq271 (σ x) (σ y)
       grind)
    | exact resolve eq4834 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4834
  have eq4840 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq661 x y
       have i₂ := eq4835
       grind)
    | exact superpose eq4835 eq661
    | (have j0 := eq661 x y
       grind)
    | exact resolve eq661 eq4835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4842 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq4835
       grind)
    | exact superpose eq4835 eq10
    | exact resolve eq10 eq4835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4914 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4804 eq4840
    | exact resolve eq4840 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4840
  have eq4915 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq271 eq4914
    | (have j1 := eq271 y x
       grind)
    | (have r₁ := eq4914
       have r₂ := eq271 (σ x) (σ y)
       grind)
    | exact resolve eq4914 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4914
  have eq4916 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4915
       have r₂ := eq4821
       grind)
    | exact resolve eq4915 eq4821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4915
  have eq4956 : (τ (σ x)) = (k y (τ (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq287 (M.op (σ x) (σ x)) y
       have i₂ := eq4827
       grind)
    | exact superpose eq4827 eq287
    | (have j0 := eq287 (σ x) x
       grind)
    | exact resolve eq287 eq4827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4827
  have eq4969 : x = (k y (τ (M.op (σ x) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4956
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4956
    | exact resolve eq4956 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956
  have eq4971 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq425 eq4969
    | (have j1 := eq425 x x
       grind)
    | exact resolve eq4969 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4969
  have eq5123 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4837
       have r₂ := eq4916
       grind)
    | exact resolve eq4837 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4837
  have eq5124 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4821
       have i₂ := eq5123
       grind)
    | exact superpose eq5123 eq4821
    | exact resolve eq4821 eq5123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4821
  have eq5126 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq5123
       grind)
    | exact superpose eq5123 eq10
    | exact resolve eq10 eq5123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5123
  have eq5202 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq5124
  have eq5266 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5126
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5126
    | exact resolve eq5126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5126
  have eq5268 : ∀ X0 : G, y = (M.op (M.op y y) (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq5266
       grind)
    | exact superpose eq5266 eq9
    | exact resolve eq9 eq5266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5271 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) (M.op X0 y)) (M.op X1 y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq61 y X1 x x
       have i₂ := eq5266
       grind)
    | exact superpose eq5266 eq61
    | exact resolve eq61 eq5266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5273 : y = (M.op (M.op y y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq5266
       grind)
    | exact superpose eq5266 eq62
    | exact resolve eq62 eq5266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5277 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) (M.op X0 y)) (M.op X1 (M.op X2 y))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3233 y X0 X2 x X1
       have i₂ := eq5266
       grind)
    | exact superpose eq5266 eq3233
    | exact resolve eq3233 eq5266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5279 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq5297 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op y (M.op X0 (M.op X1 (M.op X2 y)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3233 y y X1 X2 X0
       have i₂ := eq5268 y
       grind)
    | exact superpose eq5268 eq3233
    | exact resolve eq3233 eq5268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5349 : ∀ X0 X1 : G, (M.op y y) = (M.op y (M.op X0 (M.op X1 y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq5297 X0 X1 (M.op y y)
       have i₂ := eq5273
       grind)
    | exact superpose eq5273 eq5297
    | exact resolve eq5297 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5353 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5297 X0 (M.op y y) x
       have i₂ := eq5268 x
       grind)
    | exact superpose eq5268 eq5297
    | exact resolve eq5297 eq5268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5297
  have eq5374 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5353 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5353
  have eq5375 : ∀ X0 X1 : G, (M.op y y) = (M.op y (M.op X0 (M.op X1 y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq5349 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5349
  have eq5847 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4822 (σ x)
       have i₂ := eq4971
       grind)
    | exact superpose eq4971 eq4822
    | exact resolve eq4822 eq4971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5852 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (k y (k x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) x (σ x)
       have i₂ := eq4971
       grind)
    | exact superpose eq4971 eq9
    | exact resolve eq9 eq4971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5853 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (k y (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq4971
       grind)
    | exact superpose eq4971 eq12
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq4971
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4971
       grind)
    | exact resolve eq12 eq4971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5860 : (σ x) = (k (σ x) (σ x)) ∨ x = (k y (k x x)) ∨ x = (M.op x y) := by grind
  clear eq5853
  have eq5863 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by grind
  clear eq5847
  have eq5867 : x = (k y (k x x)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5860
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq5860
    | exact resolve eq5860 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5860
  have eq5870 : (k x x) = (M.op (k x x) y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op (k x x) y) := by
    first
    | (have i₁ := eq5867
       have i₂ := eq271 y (k x x)
       grind)
    | exact superpose eq271 eq5867
    | (have j1 := eq271 y (k x x)
       grind)
    | exact resolve eq5867 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6795 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op X2 (τ X0)))) (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq283 (k X0 X0) (M.op X1 (M.op X2 (τ X0)))
       have i₂ := eq542 X0 X1 X2
       grind)
    | exact superpose eq542 eq283
    | (have j0 := eq283 X0 (τ X0)
       have j1 := eq542 X0 X1 X2
       grind)
    | exact resolve eq283 eq542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283 eq542
  have eq6822 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op X1 (M.op X2 (τ X0)))) (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq6795 X0 X1 X2
       have j1 := eq547 X0 X0
       grind)
    | (have r₁ := eq6795 X1 X1 X2
       have r₂ := eq547 X1 X1
       grind)
    | exact resolve eq6795 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547 eq6795
  have eq6850 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 (M.op X2 (τ X0)))) (k X0 X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6822 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6822
    | (have j0 := eq6822 X0 X1 X2
       grind)
    | exact resolve eq6822 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6822
  have eq7005 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (σ (M.op X1 (M.op X2 (τ (σ X0)))))) (M.op (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq354 X0 (σ X0) (σ (M.op X1 (M.op X2 (τ (σ X0)))))
       have i₂ := eq6850 (σ X0) X1 X2
       grind)
    | exact superpose eq6850 eq354
    | (have j0 := eq354 X0 (σ X0) X2
       have j1 := eq6850 (σ X0) X1 X2
       grind)
    | exact resolve eq354 eq6850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354 eq6850
  have eq7024 : ∀ X0 X1 X2 : G, (k (τ (σ (M.op X1 (M.op X2 X0)))) (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7005 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7005
    | (have j0 := eq7005 X0 X1 X2
       grind)
    | exact resolve eq7005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005
  have eq7049 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) X0) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7024 X0 X1 X2
       have i₂ := eq10 (M.op X1 (M.op X2 X0))
       grind)
    | exact superpose eq10 eq7024
    | (have j0 := eq7024 X0 X1 X2
       grind)
    | exact resolve eq7024 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7024
  have eq7065 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (k (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7049 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7049
    | (have j0 := eq7049 X0 X1 X2
       grind)
    | exact resolve eq7049 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7049
  have eq7085 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq7065 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7065
    | (have j0 := eq7065 X0 X1 X2
       grind)
    | exact resolve eq7065 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7065
  have eq7086 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq7085 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7085
  have eq7108 : ∀ X0 : G, y = (k (M.op X0 y) (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7086 y X0 (M.op y y)
       have i₂ := eq5273
       grind)
    | exact superpose eq5273 eq7086
    | (have j0 := eq7086 y x x
       grind)
    | exact resolve eq7086 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7123 : ∀ X0 X2 : G, (M.op X2 X0) = (k X0 (M.op (M.op X2 X0) (M.op X2 X0))) ∨ (M.op X2 X0) = (M.op (M.op X2 X0) (M.op X2 X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq7086 (M.op X2 X0) (M.op X0 X0) x
       have i₂ := eq9 X0 x X2
       grind)
    | exact superpose eq9 eq7086
    | (have j0 := eq7086 (M.op X2 X0) x X2
       grind)
    | exact resolve eq7086 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7140 : ∀ X0 X1 : G, (M.op y y) = (k (M.op X0 (M.op X1 (M.op y y))) y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq7086 (M.op y y) X1 x
       have i₂ := eq5268 y
       grind)
    | exact superpose eq5268 eq7086
    | (have j0 := eq7086 y X1 x
       grind)
    | exact resolve eq7086 eq5268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7086
  have eq7196 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq555 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq555
    | (have j0 := eq555 (σ X0) (σ X1)
       grind)
    | exact resolve eq555 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq7272 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7196 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7196
    | (have j0 := eq7196 X0 X1
       grind)
    | exact resolve eq7196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7196
  have eq7309 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7272 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7272
    | (have j0 := eq7272 X0 X1
       grind)
    | exact resolve eq7272 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7272
  have eq7342 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7309 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7309
    | (have j0 := eq7309 X0 X1
       grind)
    | exact resolve eq7309 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7309
  have eq7375 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7342 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7342
    | (have j0 := eq7342 X0 X1
       grind)
    | exact resolve eq7342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7342
  have eq7392 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7375 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7375
    | (have j0 := eq7375 X0 X1
       grind)
    | exact resolve eq7375 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7375
  have eq7409 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7392 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7392
    | (have j0 := eq7392 X0 X1
       grind)
    | exact resolve eq7392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7392
  have eq7441 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7409 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7409
    | (have j0 := eq7409 (σ X0) (σ X1)
       grind)
    | exact resolve eq7409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7807 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op X0 y)) = (M.op (M.op X0 y) (M.op X1 y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq61 y (M.op X0 y) X0 X1
       have i₂ := eq5277 X0 (M.op X0 y) X0
       grind)
    | exact superpose eq5277 eq61
    | exact resolve eq61 eq5277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7861 : ∀ X0 : G, (M.op (M.op X0 y) (M.op X0 y)) = (M.op (M.op X0 y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7807 X0 (M.op y y)
       have i₂ := eq5273
       grind)
    | exact superpose eq5273 eq7807
    | exact resolve eq7807 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7867 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) (M.op X1 y)) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq62 y X0
       have i₂ := eq7807 X0 X1
       grind)
    | (have i₁ := eq62 y X1
       have i₂ := eq7807 X1 X1
       grind)
    | exact superpose eq7807 eq62
    | exact resolve eq62 eq7807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7950 : ∀ X0 : G, (M.op (M.op X0 y) (M.op X0 y)) = (M.op (M.op X0 y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7861 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7861
  have eq7962 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7867 X0 (M.op y y)
       have i₂ := eq5273
       grind)
    | exact superpose eq5273 eq7867
    | exact resolve eq7867 eq5273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5273 eq7867
  have eq8012 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) y) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq7962 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7962
  have eq8080 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) y) (M.op X1 y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq7950 eq5271
    | exact resolve eq5271 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5271
  have eq8081 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) y) (M.op X1 (M.op X2 y))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq7950 eq5277
    | exact resolve eq5277 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5277
  have eq8082 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (M.op (M.op X0 y) (M.op X1 y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq7950 eq7807
    | exact resolve eq7807 eq7950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7807 eq7950
  have eq10031 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (M.op X0 (σ X1)) = X0 ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) X1)
       have i₂ := eq4764 X0 X1
       grind)
    | exact superpose eq4764 eq10
    | (have j1 := eq4764 X0 X1
       grind)
    | exact resolve eq10 eq4764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4764
  have eq11602 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | (have i₁ := eq4822 (M.op (σ y) (σ y))
       have i₂ := eq5863
       grind)
    | exact superpose eq5863 eq4822
    | exact resolve eq4822 eq5863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11605 : (τ (σ y)) = (k x (τ (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | (have i₁ := eq287 (M.op (σ y) (σ y)) x
       have i₂ := eq5863
       grind)
    | exact superpose eq5863 eq287
    | (have j0 := eq287 (σ y) y
       grind)
    | exact resolve eq287 eq5863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11627 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by grind
  clear eq11602
  have eq11635 : y = (k x (τ (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | (have i₁ := eq11605
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq11605
    | exact resolve eq11605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11605
  have eq11639 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x (k y y)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | exact superpose eq425 eq11635
    | (have j1 := eq425 y y
       grind)
    | exact resolve eq11635 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11635
  have eq12002 : ∀ X0 : G, (M.op y y) = (k (M.op X0 y) y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7140 (M.op (M.op X0 y) y) x
       have i₂ := eq8081 X0 x y
       grind)
    | exact superpose eq8081 eq7140
    | exact resolve eq7140 eq8081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7140 eq8081
  have eq12022 : ∀ X0 : G, (M.op y y) = (k (M.op X0 y) y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12002 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12002
  have eq12341 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    intro X0
    first
    | (have i₁ := eq4825 (M.op (σ y) (σ y)) x
       have i₂ := eq5863
       grind)
    | exact superpose eq5863 eq4825
    | exact resolve eq4825 eq5863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12394 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    intro X0
    first
    | (have j0 := eq12341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12341
  have eq14160 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (k (M.op X1 y) (M.op (M.op (M.op X0 y) y) (M.op (M.op X0 y) y))) ∨ (M.op (M.op X0 y) y) = (M.op (M.op (M.op X0 y) y) (M.op (M.op X0 y) y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq7123 (M.op X1 y) (M.op X0 y)
       have i₂ := eq8082 X0 X1
       grind)
    | exact superpose eq8082 eq7123
    | (have j0 := eq7123 y (M.op X0 y)
       grind)
    | exact resolve eq7123 eq8082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14284 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (k (M.op X1 y) (M.op X0 y)) ∨ (M.op (M.op X0 y) y) = (M.op (M.op (M.op X0 y) y) (M.op (M.op X0 y) y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8080 eq14160
    | (have j0 := eq14160 X0 X1
       grind)
    | exact resolve eq14160 eq8080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14160
  have eq14297 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (k (M.op X1 y) (M.op X0 y)) ∨ (M.op X0 y) = (M.op (M.op X0 y) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq8080 eq14284
    | (have j0 := eq14284 X0 X1
       grind)
    | exact resolve eq14284 eq8080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8080 eq14284
  have eq33204 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op X0 (M.op X1 (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    intro X0 X1
    first
    | (have i₁ := eq4829 (σ y) X0 X1
       have i₂ := eq12394 (σ y)
       grind)
    | exact superpose eq12394 eq4829
    | exact resolve eq4829 eq12394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4829 eq12394
  have eq33271 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op X0 (M.op X1 (σ x)))) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    intro X0 X1
    first
    | (have j0 := eq33204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33204
  have eq49471 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) ∨ y = (k x (k y y)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | (have i₁ := eq5863
       have i₂ := eq11639
       grind)
    | exact superpose eq11639 eq5863
    | exact resolve eq5863 eq11639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5863 eq11639
  have eq49519 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) ∨ y = (k x (k y y)) := by grind
  clear eq49471
  have eq49542 : y = (k x (k y y)) ∨ x = (k y (k x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq49519
       have r₂ := eq4916
       grind)
    | exact resolve eq49519 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49519
  have eq50749 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (k y (k x x)) ∨ x = (k y (k x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq33271 X0 (σ x)
       have i₂ := eq4971
       grind)
    | exact superpose eq4971 eq33271
    | exact resolve eq33271 eq4971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4971
  have eq50754 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) ∨ x = (k y (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33271 (σ x) x
       have i₂ := eq5852 x
       grind)
    | exact superpose eq5852 eq33271
    | exact resolve eq33271 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5852 eq33271
  have eq50819 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by grind
  clear eq50754
  have eq50821 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    intro X0
    first
    | (have j0 := eq50749 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50749
  have eq50864 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | exact superpose eq50819 eq11627
    | exact resolve eq11627 eq50819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11627
  have eq50878 : (τ (M.op (σ y) (σ x))) = (k y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | (have i₁ := eq425 y y
       have i₂ := eq50819
       grind)
    | exact superpose eq50819 eq425
    | (have j0 := eq425 y x
       grind)
    | exact resolve eq425 eq50819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50895 : (τ (M.op (σ y) (σ x))) = (M.op (τ (σ y)) y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (τ (σ y)) = (M.op (τ (σ y)) y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | (have i₁ := eq10031 (σ y) y
       have i₂ := eq50819
       grind)
    | exact superpose eq50819 eq10031
    | (have j0 := eq10031 (σ y) x
       grind)
    | exact resolve eq10031 eq50819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50976 : (τ (M.op (σ y) (σ x))) = (M.op (τ (σ y)) y) ∨ (τ (σ y)) = (M.op (τ (σ y)) y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | (have r₁ := eq50895
       have r₂ := eq4916
       grind)
    | exact resolve eq50895 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50895
  have eq50987 : (τ (M.op (σ y) (σ x))) = (k y y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | (have r₁ := eq50878
       have r₂ := eq4916
       grind)
    | exact resolve eq50878 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50878
  have eq51005 : (τ (M.op (σ y) (σ x))) = (M.op y y) ∨ (τ (σ y)) = (M.op (τ (σ y)) y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | (have i₁ := eq50976
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq50976
    | exact resolve eq50976 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50976
  have eq51011 : x = (k y (k x x)) ∨ x = (M.op x y) ∨ (k x y) = (k y y) := by
    first
    | exact superpose eq4842 eq50987
    | exact resolve eq50987 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50987
  have eq51024 : y = (M.op y y) ∨ (τ (M.op (σ y) (σ x))) = (M.op y y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    first
    | (have i₁ := eq51005
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq51005
    | exact resolve eq51005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51005
  have eq51035 : x = (k y (k x x)) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq4842 eq51024
    | exact resolve eq51024 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51024
  have eq51040 : y = (k x (k x y)) ∨ x = (k y (k x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51011 eq49542
    | exact resolve eq49542 eq51011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49542
  have eq51053 : x ≠ (k x x) ∨ (k x x) = (M.op (k x x) y) ∨ x = (M.op x y) ∨ (k x y) = (k y y) := by
    first
    | (have i₁ := eq571 y (k x x)
       have i₂ := eq51011
       grind)
    | exact superpose eq51011 eq571
    | (have j0 := eq571 x x
       grind)
    | exact resolve eq571 eq51011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51064 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (k x x))) ∨ x = (M.op x y) ∨ (k x y) = (k y y) := by
    first
    | (have i₁ := eq7441 y (k x x)
       have i₂ := eq51011
       grind)
    | exact superpose eq51011 eq7441
    | (have j0 := eq7441 x x
       grind)
    | exact resolve eq7441 eq51011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51011
  have eq51066 : (σ x) ≠ (σ (k x x)) ∨ (σ y) = (M.op (σ y) (σ (k x x))) ∨ x = (M.op x y) ∨ (k x y) = (k y y) := by
    first
    | (have r₁ := eq51064
       have r₂ := eq5202
       grind)
    | exact resolve eq51064 eq5202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51064
  have eq51071 : x ≠ (k x x) ∨ (M.op x x) = (M.op (M.op x x) y) ∨ x = (M.op x y) ∨ (k x y) = (k y y) := by
    first
    | exact superpose eq648 eq51053
    | (have j1 := eq648 x x
       grind)
    | exact resolve eq51053 eq648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51053
  have eq51073 : (σ x) ≠ (σ (k x x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ (k x y) = (k y y) := by
    first
    | exact superpose eq661 eq51066
    | (have j1 := eq661 x x
       grind)
    | exact resolve eq51066 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51066
  have eq51078 : x ≠ (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (k x y) = (k y y) := by
    first
    | exact superpose eq571 eq51071
    | (have j1 := eq571 x x
       grind)
    | exact resolve eq51071 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51071
  have eq51079 : x ≠ (k x x) ∨ x = (M.op x y) ∨ (k x y) = (k y y) := by grind
  clear eq51078
  have eq51080 : (σ x) ≠ (σ (k x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (k x y) = (k y y) := by
    first
    | exact superpose eq573 eq51073
    | (have j1 := eq573 x x
       grind)
    | exact resolve eq51073 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51073
  have eq51083 : (σ x) ≠ (σ (k x x)) ∨ x = (M.op x y) ∨ (k x y) = (k y y) := by
    first
    | (have r₁ := eq51080
       have r₂ := eq4916
       grind)
    | exact resolve eq51080 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51080
  have eq52135 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ (k x x))) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7441 y (k x x)
       have i₂ := eq51035
       grind)
    | exact superpose eq51035 eq7441
    | (have j0 := eq7441 x x
       grind)
    | exact resolve eq7441 eq51035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51035
  have eq52137 : (σ x) ≠ (σ (k x x)) ∨ (σ y) = (M.op (σ y) (σ (k x x))) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq52135
       have r₂ := eq5202
       grind)
    | exact resolve eq52135 eq5202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52135
  have eq52143 : (σ x) ≠ (σ (k x x)) ∨ (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq661 eq52137
    | (have j1 := eq661 x x
       grind)
    | exact resolve eq52137 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52137
  have eq52150 : (σ x) ≠ (σ (k x x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq573 eq52143
    | (have j1 := eq573 x x
       grind)
    | exact resolve eq52143 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52143
  have eq52153 : (σ x) ≠ (σ (k x x)) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq52150
       have r₂ := eq4916
       grind)
    | exact resolve eq52150 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52150
  have eq52411 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    intro X0
    first
    | exact superpose eq50819 eq50821
    | exact resolve eq50821 eq50819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50821
  have eq52691 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) = (k (τ (M.op X0 (σ x))) y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    intro X0
    first
    | (have i₁ := eq278 y (M.op X0 (σ x))
       have i₂ := eq52411 X0
       grind)
    | exact superpose eq52411 eq278
    | (have j0 := eq278 y (σ x)
       grind)
    | exact resolve eq278 eq52411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278 eq52411
  have eq52772 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) = (k (τ (M.op X0 (σ x))) y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    intro X0
    first
    | (have j0 := eq52691 X0
       grind)
    | (have r₁ := eq52691 X0
       have r₂ := eq4916
       grind)
    | exact resolve eq52691 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52691
  have eq52781 : ∀ X0 : G, (k x y) = (k (τ (M.op X0 (σ x))) y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by
    intro X0
    first
    | exact superpose eq4842 eq52772
    | exact resolve eq52772 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52772
  have eq52809 : (k x y) = (k (k x y) y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52781 (σ y)
       have i₂ := eq4842
       grind)
    | exact superpose eq4842 eq52781
    | exact resolve eq52781 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52781
  have eq52875 : (k x y) = (k (k x y) y) ∨ x = (M.op x y) ∨ x = (k y (k x x)) := by grind
  clear eq52809
  have eq73804 : (k x x) ≠ (k x x) ∨ y = (M.op y (k x x)) ∨ y = (k y (k x x)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op (k x x) y) := by
    first
    | (have i₁ := eq13 y (k x x)
       have i₂ := eq5870
       grind)
    | exact superpose eq5870 eq13
    | (have j0 := eq13 y (k x x)
       grind)
    | (have r₁ := eq13 y (k x x)
       have r₂ := eq5870
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq5870
       grind)
    | exact resolve eq13 eq5870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5870
  have eq73827 : y = (M.op y (k x x)) ∨ y = (k y (k x x)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op (k x x) y) := by grind
  clear eq73804
  have eq73899 : y = (M.op y (k x x)) ∨ x = y ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op (k x x) y) := by
    first
    | exact superpose eq5867 eq73827
    | exact resolve eq73827 eq5867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73827
  have eq73915 : y = (M.op y (k x x)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op (k x x) y) := by
    first
    | (have r₁ := eq73899
       have r₂ := eq5279
       grind)
    | exact resolve eq73899 eq5279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73899
  have eq73919 : y ≠ y ∨ (k y (k x x)) = (M.op (k x x) y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op (k x x) y) := by
    first
    | (have i₁ := eq12 y (k x x)
       have i₂ := eq73915
       grind)
    | exact superpose eq73915 eq12
    | (have j0 := eq12 y (k x x)
       grind)
    | (have r₁ := eq12 y (k x x)
       have r₂ := eq73915
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq73915
       grind)
    | exact resolve eq12 eq73915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73915
  have eq73943 : (k y (k x x)) = (M.op (k x x) y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op (k x x) y) := by grind
  clear eq73919
  have eq73949 : x = (M.op (k x x) y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op (k x x) y) := by
    first
    | exact superpose eq5867 eq73943
    | exact resolve eq73943 eq5867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5867 eq73943
  have eq73950 : x = (M.op (k x x) y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by grind
  clear eq73949
  have eq73962 : (M.op y x) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5374 (k x x)
       have i₂ := eq73950
       grind)
    | exact superpose eq73950 eq5374
    | exact resolve eq5374 eq73950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73963 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5375 X0 (k x x)
       have i₂ := eq73950
       grind)
    | exact superpose eq73950 eq5375
    | exact resolve eq5375 eq73950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5375
  have eq73968 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8012 (k x x)
       have i₂ := eq73950
       grind)
    | exact superpose eq73950 eq8012
    | exact resolve eq8012 eq73950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8012
  have eq73973 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8082 (k x x) x
       have i₂ := eq73950
       grind)
    | exact superpose eq73950 eq8082
    | exact resolve eq8082 eq73950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8082
  have eq73991 : (k x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12022 (k x x)
       have i₂ := eq73950
       grind)
    | exact superpose eq73950 eq12022
    | exact resolve eq12022 eq73950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12022
  have eq74013 : ∀ X0 : G, (M.op x y) = (k (M.op X0 y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq14297 (k x x) x
       have i₂ := eq73950
       grind)
    | exact superpose eq73950 eq14297
    | exact resolve eq14297 eq73950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14297
  have eq74027 : x = (M.op (M.op x x) y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62 y (k x x)
       have i₂ := eq73950
       grind)
    | exact superpose eq73950 eq62
    | exact resolve eq62 eq73950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74067 : ∀ X0 : G, (M.op x y) = (k (M.op X0 y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq74013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74013
  have eq74089 : (k x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq73991
  have eq74107 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq73973 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73973
  have eq74112 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) := by grind
  clear eq73968
  have eq74117 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | (have j0 := eq73963 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73963
  have eq74118 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq73962
  have eq74142 : ∀ X0 : G, y = (k (M.op X0 y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | exact superpose eq5266 eq74067
    | exact resolve eq74067 eq5266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74067
  have eq74144 : (k x y) = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq74089
       have r₂ := eq52153
       grind)
    | exact resolve eq74089 eq52153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52153 eq74089
  have eq74150 : ∀ X0 : G, y = (M.op x (M.op X0 y)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | exact superpose eq5266 eq74107
    | exact resolve eq74107 eq5266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74107
  have eq74153 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq5266 eq74112
    | exact resolve eq74112 eq5266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5266 eq74112
  have eq74553 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq573 x y
       have i₂ := eq74144
       grind)
    | exact superpose eq74144 eq573
    | (have j0 := eq573 x y
       grind)
    | exact resolve eq573 eq74144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74589 : (σ y) ≠ (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq74553
       have r₂ := eq4916
       grind)
    | exact resolve eq74553 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74553
  have eq74601 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ (k x y) = (k y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq51083
       have i₂ := eq74153
       grind)
    | exact superpose eq74153 eq51083
    | (have r₁ := eq51083
       have r₂ := eq74153
       grind)
    | exact resolve eq51083 eq74153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74612 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq74153
       grind)
    | exact superpose eq74153 eq10
    | exact resolve eq10 eq74153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74153
  have eq74778 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ (k x y) = (k y y) ∨ x = (M.op y y) := by grind
  clear eq74601
  have eq74779 : (k x y) = (k y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq74778
  have eq74887 : x = (k x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq74612
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq74612
    | exact resolve eq74612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74612
  have eq74943 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq648 x x
       have i₂ := eq74887
       grind)
    | exact superpose eq74887 eq648
    | (have r₁ := eq648 x x
       have r₂ := eq74887
       grind)
    | exact resolve eq648 eq74887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74887
  have eq74957 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq74943
  have eq75038 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5268 y
       have i₂ := eq74957
       grind)
    | exact superpose eq74957 eq5268
    | exact resolve eq5268 eq74957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75043 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq5374 y
       have i₂ := eq74957
       grind)
    | exact superpose eq74957 eq5374
    | exact resolve eq5374 eq74957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75048 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7108 y
       have i₂ := eq74957
       grind)
    | exact superpose eq74957 eq7108
    | exact resolve eq7108 eq74957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7108 eq74957
  have eq75211 : y = (k x x) ∨ x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq75048
  have eq75216 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq75043
  have eq75221 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq75038
  have eq75295 : y = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq75211
       have r₂ := eq5279
       grind)
    | exact resolve eq75211 eq5279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75211
  have eq76736 : y ≠ (k x y) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq648 y y
       have i₂ := eq74779
       grind)
    | exact superpose eq74779 eq648
    | (have j0 := eq648 x y
       grind)
    | exact resolve eq648 eq74779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648 eq74779
  have eq76760 : y ≠ (k x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7409 eq76736
    | (have j1 := eq7409 x y
       grind)
    | exact resolve eq76736 eq7409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7409 eq76736
  have eq76761 : y ≠ (k x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq76760
  have eq81834 : y = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74142 (k x x)
       have i₂ := eq73950
       grind)
    | exact superpose eq73950 eq74142
    | exact resolve eq74142 eq73950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73950 eq74142
  have eq81866 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ y = (k x x) := by grind
  clear eq81834
  have eq81881 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ (k x y) = (k y y) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq51083
       have i₂ := eq81866
       grind)
    | exact superpose eq81866 eq51083
    | (have r₁ := eq51083
       have r₂ := eq81866
       grind)
    | exact resolve eq51083 eq81866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51083
  have eq81888 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq661 x x
       have i₂ := eq81866
       grind)
    | exact superpose eq81866 eq661
    | (have r₁ := eq661 x x
       have r₂ := eq81866
       grind)
    | exact resolve eq661 eq81866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81866
  have eq82058 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (k x x) := by grind
  clear eq81888
  have eq82062 : (σ x) ≠ (σ x) ∨ x = (M.op x y) ∨ (k x y) = (k y y) ∨ y = (k x x) := by grind
  clear eq81881
  have eq82063 : (k x y) = (k y y) ∨ x = (M.op x y) ∨ y = (k x x) := by grind
  clear eq82062
  have eq82318 : y ≠ (k x y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | (have i₁ := eq571 y y
       have i₂ := eq82063
       grind)
    | exact superpose eq82063 eq571
    | (have j0 := eq571 x y
       grind)
    | exact resolve eq571 eq82063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82063
  have eq82351 : y ≠ (k x y) ∨ x = y ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | exact superpose eq76761 eq82318
    | exact resolve eq82318 eq76761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76761 eq82318
  have eq82365 : y ≠ (k x y) ∨ x = (M.op x y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq82351
       have r₂ := eq5279
       grind)
    | exact resolve eq82351 eq5279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82351
  have eq82424 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ y = (k x x) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) x (σ x)
       have i₂ := eq82058
       grind)
    | exact superpose eq82058 eq9
    | exact resolve eq9 eq82058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82058
  have eq83238 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74150 (M.op x x)
       have i₂ := eq74027
       grind)
    | exact superpose eq74027 eq74150
    | exact resolve eq74150 eq74027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74027 eq74150
  have eq83366 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq83238
  have eq83880 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq661 x x
       have i₂ := eq83366
       grind)
    | exact superpose eq83366 eq661
    | (have r₁ := eq661 x x
       have r₂ := eq83366
       grind)
    | exact resolve eq661 eq83366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83366
  have eq84052 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq83880
  have eq85081 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq4822 (σ x)
       have i₂ := eq84052
       grind)
    | exact superpose eq84052 eq4822
    | exact resolve eq4822 eq84052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84052
  have eq85155 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq85081
  have eq89974 : ∀ X0 : G, (M.op y x) = (M.op y (M.op X0 x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) := by
    intro X0
    first
    | exact superpose eq74118 eq74117
    | exact resolve eq74117 eq74118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74117 eq74118
  have eq91530 : x = (M.op (M.op x x) (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq9 x y x
       have i₂ := eq89974 x
       grind)
    | exact superpose eq89974 eq9
    | exact resolve eq9 eq89974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89974
  have eq93176 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op y x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op y x))) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ (k x x)) := by
    first
    | (have i₁ := eq4797 (M.op x x) (M.op y x)
       have i₂ := eq91530
       grind)
    | exact superpose eq91530 eq4797
    | (have j0 := eq4797 (M.op x x) (M.op y x)
       grind)
    | exact resolve eq4797 eq91530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4797 eq91530
  have eq93206 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (M.op y x))) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op y x))) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | exact superpose eq271 eq93176
    | (have j1 := eq271 (σ (M.op y x)) (σ (M.op x x))
       grind)
    | exact resolve eq93176 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93176
  have eq93230 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op y x))) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | exact superpose eq75216 eq93206
    | exact resolve eq93206 eq75216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93206
  have eq93240 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | exact superpose eq75216 eq93230
    | exact resolve eq93230 eq75216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75216 eq93230
  have eq93250 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | exact superpose eq75221 eq93240
    | exact resolve eq93240 eq75221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93240
  have eq93259 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq93250
       have r₂ := eq4916
       grind)
    | exact resolve eq93250 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93250
  have eq93268 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq75221 eq93259
    | exact resolve eq93259 eq75221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75221 eq93259
  have eq93276 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq93268
       have r₂ := eq5202
       grind)
    | exact resolve eq93268 eq5202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93268
  have eq95489 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4822 (M.op (σ x) (σ x))
       have i₂ := eq93276
       grind)
    | exact superpose eq93276 eq4822
    | exact resolve eq4822 eq93276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93276
  have eq95588 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq95489
  have eq100364 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq95588 eq85155
    | exact resolve eq85155 eq95588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85155 eq95588
  have eq100501 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq100364
       have r₂ := eq5279
       grind)
    | exact resolve eq100364 eq5279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100364
  have eq100581 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4822 (M.op (σ y) (σ y))
       have i₂ := eq100501
       grind)
    | exact superpose eq100501 eq4822
    | exact resolve eq4822 eq100501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100618 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) X0 (M.op (σ y) (σ y))
       have i₂ := eq100501
       grind)
    | exact superpose eq100501 eq9
    | exact resolve eq9 eq100501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100501
  have eq100683 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq100581
  have eq100905 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4828 X0 (M.op (σ x) (σ x)) x
       have i₂ := eq100618 x
       grind)
    | exact superpose eq100618 eq4828
    | exact resolve eq4828 eq100618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4828 eq100618
  have eq100983 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq100905 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100905
  have eq101453 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4825 (σ x) X0
       have i₂ := eq100983 (σ x)
       grind)
    | exact superpose eq100983 eq4825
    | exact resolve eq4825 eq100983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4825 eq100983
  have eq101554 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq101453 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101453
  have eq101679 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101554 (M.op (σ y) (σ y))
       have i₂ := eq100683
       grind)
    | exact superpose eq100683 eq101554
    | exact resolve eq101554 eq100683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100683 eq101554
  have eq101799 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq101679
  have eq101828 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4804 eq101799
    | exact resolve eq101799 eq4804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4804 eq101799
  have eq101923 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq101828
       grind)
    | exact superpose eq101828 eq12
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq101828
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq101828
       grind)
    | exact resolve eq12 eq101828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101828
  have eq101943 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq101923
  have eq101979 : (σ x) = (σ (k x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq101943
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq101943
    | exact resolve eq101943 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101943
  have eq102008 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq101979
       grind)
    | exact superpose eq101979 eq10
    | exact resolve eq10 eq101979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101979
  have eq102308 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102008
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq102008
    | exact resolve eq102008 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102008
  have eq102356 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq102308 eq50819
    | exact resolve eq50819 eq102308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50819
  have eq102358 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq102308 eq50864
    | exact resolve eq50864 eq102308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50864
  have eq102367 : y = (k x (k x y)) ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102308 eq51040
    | exact resolve eq51040 eq102308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51040
  have eq102369 : (k x y) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq51079
       have r₂ := eq102308
       grind)
    | exact resolve eq51079 eq102308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51079
  have eq102386 : (k x y) = (k (k x y) y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq102308 eq52875
    | exact resolve eq52875 eq102308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52875
  have eq102405 : x = y ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq102308 eq75295
    | exact resolve eq75295 eq102308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75295
  have eq102408 : y ≠ (k x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102308 eq82365
    | exact resolve eq82365 eq102308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82365
  have eq102409 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq102308 eq82424
    | (have j0 := eq82424 X0
       grind)
    | exact resolve eq82424 eq102308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82424 eq102308
  have eq102486 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq102409 X0
       grind)
    | (have r₁ := eq102409 X0
       have r₂ := eq5279
       grind)
    | exact resolve eq102409 eq5279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102409
  have eq102487 : y ≠ (k x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq102408
       have r₂ := eq5279
       grind)
    | exact resolve eq102408 eq5279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102408
  have eq102490 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq102405
       have r₂ := eq5279
       grind)
    | exact resolve eq102405 eq5279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5279 eq102405
  have eq102509 : (k x y) = (k (k x y) y) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq571 y x
       grind)
    | (have r₁ := eq102386
       have r₂ := eq571 y x
       grind)
    | exact resolve eq102386 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102386
  have eq102525 : y = (k x (k x y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq571 y x
       grind)
    | (have r₁ := eq102367
       have r₂ := eq571 y x
       grind)
    | exact resolve eq102367 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102367
  have eq102534 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq571 y x
       grind)
    | (have r₁ := eq102358
       have r₂ := eq571 y x
       grind)
    | exact resolve eq102358 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102358
  have eq102536 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq571 y x
       grind)
    | (have r₁ := eq102356
       have r₂ := eq571 y x
       grind)
    | exact resolve eq102356 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq102356
  have eq105747 : (τ (σ y)) = (M.op (τ (M.op (σ y) (σ x))) y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (τ (M.op (σ y) (σ x))) = (M.op (τ (M.op (σ y) (σ x))) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10031 (M.op (σ y) (σ x)) y
       have i₂ := eq102534
       grind)
    | exact superpose eq102534 eq10031
    | (have j0 := eq10031 (σ y) x
       grind)
    | exact resolve eq10031 eq102534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102534
  have eq105804 : (τ (σ y)) = (M.op (τ (M.op (σ y) (σ x))) y) ∨ (τ (M.op (σ y) (σ x))) = (M.op (τ (M.op (σ y) (σ x))) y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq105747
       have r₂ := eq4916
       grind)
    | exact resolve eq105747 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105747
  have eq105816 : y = (M.op (τ (M.op (σ y) (σ x))) y) ∨ (τ (M.op (σ y) (σ x))) = (M.op (τ (M.op (σ y) (σ x))) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq105804
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq105804
    | exact resolve eq105804 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105804
  have eq105826 : y = (M.op (k x y) y) ∨ (τ (M.op (σ y) (σ x))) = (M.op (τ (M.op (σ y) (σ x))) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4842 eq105816
    | exact resolve eq105816 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105816
  have eq105835 : (k x y) = (M.op (k x y) y) ∨ y = (M.op (k x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4842 eq105826
    | exact resolve eq105826 eq4842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4842 eq105826
  have eq106553 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ x)) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq102536 eq4822
    | exact resolve eq4822 eq102536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4822 eq102536
  have eq117787 : (M.op y y) = (M.op y (k x y)) ∨ x = (M.op x y) ∨ y = (M.op (k x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5374 (k x y)
       have i₂ := eq105835
       grind)
    | exact superpose eq105835 eq5374
    | exact resolve eq5374 eq105835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5374
  have eq117851 : (k x y) ≠ (k x y) ∨ (M.op y (k x y)) = (k (k x y) y) ∨ y = (M.op (k x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (k x y) y
       have i₂ := eq105835
       grind)
    | exact superpose eq105835 eq12
    | (have j0 := eq12 (k x y) y
       grind)
    | (have r₁ := eq12 (k x y) y
       have r₂ := eq105835
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq105835
       grind)
    | exact resolve eq12 eq105835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105835
  have eq117876 : (M.op y (k x y)) = (k (k x y) y) ∨ y = (M.op (k x y) y) ∨ x = (M.op x y) := by grind
  clear eq117851
  have eq117936 : (M.op y y) = (M.op y (k x y)) ∨ x = (M.op x y) ∨ y = (M.op (k x y) y) := by grind
  clear eq117787
  have eq117949 : (k x y) = (M.op y (k x y)) ∨ y = (M.op (k x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102509 eq117876
    | exact resolve eq117876 eq102509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102509 eq117876
  have eq120917 : y = (M.op (k x y) y) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq117936 eq117949
    | exact resolve eq117949 eq117936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117936 eq117949
  have eq120995 : y ≠ (M.op y y) ∨ (k (M.op y y) y) = (M.op y (M.op y y)) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq66 (k x y) y
       have i₂ := eq120917
       grind)
    | exact superpose eq120917 eq66
    | exact resolve eq66 eq120917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120917
  have eq121105 : (k (M.op y y) y) = (M.op y (M.op y y)) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq120995
       have r₂ := eq74144
       grind)
    | exact resolve eq120995 eq74144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120995
  have eq121122 : (M.op y y) = (k y y) ∨ (k x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74144 eq121105
    | exact resolve eq121105 eq74144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74144 eq121105
  have eq121132 : (M.op y y) = (k y y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq271 eq121122
    | (have j1 := eq271 y y
       grind)
    | exact resolve eq121122 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121122
  have eq121139 : (M.op y y) = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq121132
       have r₂ := eq102487
       grind)
    | exact resolve eq121132 eq102487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102487 eq121132
  have eq121355 : (k x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121139 eq102369
    | exact resolve eq102369 eq121139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102369 eq121139
  have eq121420 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121355 eq4835
    | exact resolve eq4835 eq121355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4835
  have eq121447 : y = (k x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq121355 eq102525
    | exact resolve eq102525 eq121355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102525
  have eq121531 : (σ y) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq573 x (M.op y y)
       have i₂ := eq121447
       grind)
    | exact superpose eq121447 eq573
    | (have j0 := eq573 x (M.op y y)
       grind)
    | exact resolve eq573 eq121447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121447
  have eq121549 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74589 eq121531
    | exact resolve eq121531 eq74589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74589 eq121531
  have eq121554 : (σ y) ≠ (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq121549
       have r₂ := eq4916
       grind)
    | exact resolve eq121549 eq4916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4916 eq121549
  have eq121725 : ∀ X0 : G, (σ y) = (M.op (σ (M.op y y)) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq121420 eq106553
    | exact resolve eq106553 eq121420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106553
  have eq121770 : (M.op (τ (σ y)) x) = (τ (σ (M.op y y))) ∨ (σ y) = (σ (M.op y y)) ∨ (τ (σ y)) = (M.op (τ (σ y)) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10031 (σ y) x
       have i₂ := eq121420
       grind)
    | exact superpose eq121420 eq10031
    | (have j0 := eq10031 (σ y) x
       grind)
    | exact resolve eq10031 eq121420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121420
  have eq121836 : (M.op (τ (σ y)) x) = (τ (σ (M.op y y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq121770
       have r₂ := eq121554
       grind)
    | exact resolve eq121770 eq121554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121554 eq121770
  have eq121873 : (M.op (τ (σ y)) x) = (M.op y y) ∨ (τ (σ y)) = (M.op (τ (σ y)) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121836
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq121836
    | exact resolve eq121836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121836
  have eq121904 : (M.op y x) = (M.op y y) ∨ (τ (σ y)) = (M.op (τ (σ y)) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121873
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq121873
    | exact resolve eq121873 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121873
  have eq121921 : (M.op y x) = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121904
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq121904
    | exact resolve eq121904 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121904
  have eq124587 : y = (M.op (M.op y x) (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5268 y
       have i₂ := eq121921
       grind)
    | exact superpose eq121921 eq5268
    | exact resolve eq5268 eq121921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5268 eq121921
  have eq124797 : y = (M.op (M.op y x) (M.op y x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq124587
  have eq129787 : x = (M.op (M.op x x) y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq9 x (M.op y x) y
       have i₂ := eq124797
       grind)
    | exact superpose eq124797 eq9
    | exact resolve eq9 eq124797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124797
  have eq129905 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq102490 eq129787
    | exact resolve eq129787 eq102490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102490 eq129787
  have eq129906 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq129905
  have eq129927 : y ≠ y ∨ x = (M.op x y) ∨ x = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq129906
       grind)
    | exact superpose eq129906 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq129906
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq129906
       grind)
    | exact resolve eq13 eq129906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129906
  have eq129949 : y ≠ y ∨ x = (M.op x y) ∨ x = (k x y) := by grind
  clear eq129927
  have eq129950 : x = (k x y) ∨ x = (M.op x y) := by grind
  clear eq129949
  have eq129966 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq129950 eq121355
    | exact resolve eq121355 eq129950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121355 eq129950
  have eq130066 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq129966 eq121725
    | exact resolve eq121725 eq129966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121725 eq129966
  have eq130286 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq102486 eq130066
    | exact resolve eq130066 eq102486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102486 eq130066
  have eq130331 : x = (M.op x y) := by
    first
    | (have r₁ := eq130286
       have r₂ := eq5202
       grind)
    | exact resolve eq130286 eq5202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5202 eq130286
  have eq130354 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq130331
       grind)
    | exact superpose eq130331 eq16
    | exact resolve eq16 eq130331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130358 : ∀ X0 : G, y = (M.op (M.op y y) (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq130331
       grind)
    | exact superpose eq130331 eq9
    | exact resolve eq9 eq130331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130359 : x ≠ x ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq130331
       grind)
    | exact superpose eq130331 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq130331
       grind)
    | exact resolve eq12 eq130331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130360 : x ≠ x ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq130331
       grind)
    | exact superpose eq130331 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq130331
       grind)
    | exact resolve eq13 eq130331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130361 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op X0 x) (M.op X0 x)) (M.op X1 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 y X1 x x
       have i₂ := eq130331
       grind)
    | exact superpose eq130331 eq61
    | exact resolve eq61 eq130331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130363 : x = (M.op (M.op x x) y) := by
    first
    | (have i₁ := eq62 y x
       have i₂ := eq130331
       grind)
    | exact superpose eq130331 eq62
    | exact resolve eq62 eq130331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130367 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) (M.op X0 y)) (M.op X1 (M.op X2 x))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3233 y X0 X2 x X1
       have i₂ := eq130331
       grind)
    | exact superpose eq130331 eq3233
    | exact resolve eq3233 eq130331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130382 : y = (k y x) ∨ y = (M.op y x) := by grind
  clear eq130360
  have eq130383 : (k x y) = (M.op y x) := by grind
  clear eq130359
  have eq130874 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq272 x y
       have i₂ := eq130383
       grind)
    | exact superpose eq130383 eq272
    | (have j0 := eq272 x y
       grind)
    | exact resolve eq272 eq130383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130895 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7441 x y
       have i₂ := eq130383
       grind)
    | exact superpose eq130383 eq7441
    | (have j0 := eq7441 x y
       grind)
    | exact resolve eq7441 eq130383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7441 eq130383
  have eq130897 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (σ (M.op y x)) := by
    first
    | (have r₁ := eq130895
       have r₂ := eq130354
       grind)
    | exact resolve eq130895 eq130354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130895
  have eq130955 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq272 y x
       have i₂ := eq130382
       grind)
    | exact superpose eq130382 eq272
    | (have j0 := eq272 y x
       grind)
    | exact resolve eq272 eq130382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272 eq130382
  have eq130983 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq130955
       have r₂ := eq130354
       grind)
    | exact resolve eq130955 eq130354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130955
  have eq131101 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq62 (σ y) (σ x)
       have i₂ := eq130983
       grind)
    | exact superpose eq130983 eq62
    | exact resolve eq62 eq130983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131110 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) (M.op X1 (M.op X2 (σ y)))) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3233 (σ y) X0 X2 (σ x) X1
       have i₂ := eq130983
       grind)
    | exact superpose eq130983 eq3233
    | exact resolve eq3233 eq130983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3233
  have eq133599 : (τ (σ y)) = (k y (τ (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq287 (M.op (σ y) (σ y)) y
       have i₂ := eq131101
       grind)
    | exact superpose eq131101 eq287
    | (have j0 := eq287 (σ y) y
       grind)
    | exact resolve eq287 eq131101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq133653 : y = (k y (τ (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq133599
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq133599
    | exact resolve eq133599 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133599
  have eq133661 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k y (k y y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq425 eq133653
    | (have j1 := eq425 y y
       grind)
    | exact resolve eq133653 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq133653
  have eq133786 : (σ (M.op y x)) = (M.op (M.op (σ (M.op y x)) (σ (M.op y x))) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq62 (σ x) (σ y)
       have i₂ := eq130874
       grind)
    | exact superpose eq130874 eq62
    | exact resolve eq62 eq130874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130874
  have eq173446 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op X1 (σ y))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ y) (M.op X0 (σ y)) X0 X1
       have i₂ := eq131110 X0 (M.op X0 (σ y)) X0
       grind)
    | exact superpose eq131110 eq61
    | exact resolve eq61 eq131110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131110
  have eq173590 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq173446 X0 (σ x)
       have i₂ := eq130983
       grind)
    | exact superpose eq130983 eq173446
    | exact resolve eq173446 eq130983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173597 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) (M.op X1 (σ y))) (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ y) X0
       have i₂ := eq173446 X0 X1
       grind)
    | (have i₁ := eq62 (σ y) X1
       have i₂ := eq173446 X1 X1
       grind)
    | exact superpose eq173446 eq62
    | exact resolve eq62 eq173446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq173446
  have eq173809 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq173590 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173590
  have eq173842 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq173597 X0 (σ x)
       have i₂ := eq130983
       grind)
    | exact superpose eq130983 eq173597
    | exact resolve eq173597 eq130983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173597
  have eq173945 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq173842 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173842
  have eq174186 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) ≠ (M.op (M.op (M.op X0 (σ y)) (σ y)) (M.op (M.op X0 (σ y)) (σ y))) ∨ (k (M.op (M.op (M.op X0 (σ y)) (σ y)) (M.op (M.op X0 (σ y)) (σ y))) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (M.op X0 (σ y)) (σ y)) (M.op (M.op X0 (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq66 (M.op X0 (σ y)) (M.op X0 (σ y))
       have i₂ := eq173809 X0
       grind)
    | exact superpose eq173809 eq66
    | (have j0 := eq66 (M.op X0 (σ y)) (σ y)
       grind)
    | exact resolve eq66 eq173809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174222 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (M.op (M.op (M.op X0 (σ y)) (σ y)) (M.op (M.op X0 (σ y)) (σ y)))) ∨ (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ y)) (M.op (M.op X0 (σ y)) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq7123 (M.op X0 (σ y)) (M.op X0 (σ y))
       have i₂ := eq173809 X0
       grind)
    | exact superpose eq173809 eq7123
    | (have j0 := eq7123 (σ y) (M.op X0 (σ y))
       grind)
    | exact resolve eq7123 eq173809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7123
  have eq174241 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y))) ∨ (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ y)) (M.op (M.op X0 (σ y)) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq173809 eq174222
    | (have j0 := eq174222 X0
       grind)
    | exact resolve eq174222 eq173809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174222
  have eq174249 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) ≠ (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) ∨ (k (M.op (M.op (M.op X0 (σ y)) (σ y)) (M.op (M.op X0 (σ y)) (σ y))) (M.op X0 (σ y))) = (M.op (M.op X0 (σ y)) (M.op (M.op (M.op X0 (σ y)) (σ y)) (M.op (M.op X0 (σ y)) (σ y)))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq173809 eq174186
    | (have j0 := eq174186 X0
       grind)
    | exact resolve eq174186 eq173809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174186
  have eq174266 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y))) ∨ (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq173809 eq174241
    | (have j0 := eq174241 X0
       grind)
    | exact resolve eq174241 eq173809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174241
  have eq174271 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) ≠ (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) ∨ (M.op (M.op X0 (σ y)) (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y))) = (k (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq173809 eq174249
    | (have j0 := eq174249 X0
       grind)
    | exact resolve eq174249 eq173809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174249
  have eq174280 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (M.op X0 (σ y))) ∨ (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq173945 eq174266
    | (have j0 := eq174266 X0
       grind)
    | exact resolve eq174266 eq173945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174266
  have eq174283 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (M.op (M.op X0 (σ y)) (σ y)) ∨ (M.op (M.op X0 (σ y)) (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y))) = (k (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ y)) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq173945 eq174271
    | (have j0 := eq174271 X0
       grind)
    | exact resolve eq174271 eq173945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174271
  have eq174286 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (M.op X0 (σ y))) ∨ (M.op X0 (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq173945 eq174280
    | (have j0 := eq174280 X0
       grind)
    | exact resolve eq174280 eq173945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174280
  have eq174289 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (M.op (M.op X0 (σ y)) (σ y)) ∨ (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) = (k (M.op X0 (σ y)) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq173945 eq174283
    | (have j0 := eq174283 X0
       grind)
    | exact resolve eq174283 eq173945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173945 eq174283
  have eq174293 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (M.op (M.op X0 (σ y)) (σ y)) ∨ (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq173809 eq174289
    | (have j0 := eq174289 X0
       grind)
    | exact resolve eq174289 eq173809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173809 eq174289
  have eq174296 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (k (M.op X0 (σ y)) (M.op X0 (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq174293 X0
       have j1 := eq174286 X0
       grind)
    | (have r₁ := eq174293 X0
       have r₂ := eq174286 X0
       grind)
    | exact resolve eq174293 eq174286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174286 eq174293
  have eq175426 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq174296 (σ x)
       have i₂ := eq130983
       grind)
    | exact superpose eq130983 eq174296
    | exact resolve eq174296 eq130983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130983
  have eq175493 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq175426
  have eq175511 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq175493
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq175493
    | exact resolve eq175493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175493
  have eq175547 : (τ (M.op (σ y) (σ y))) = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq175511
       grind)
    | exact superpose eq175511 eq10
    | exact resolve eq10 eq175511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175548 : ∀ X0 : G, (σ (k (k y y) X0)) = (k (M.op (σ y) (σ y)) (σ X0)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq15 (k y y) X0
       have i₂ := eq175511
       grind)
    | exact superpose eq175511 eq15
    | exact resolve eq15 eq175511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175881 : (τ (σ y)) = (k y y) ∨ y = (M.op y x) ∨ y = (k y (k y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq175547
       have i₂ := eq133661
       grind)
    | exact superpose eq133661 eq175547
    | exact resolve eq175547 eq133661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133661 eq175547
  have eq176090 : (τ (σ y)) = (k y y) ∨ y = (M.op y x) ∨ y = (k y (k y y)) := by grind
  clear eq175881
  have eq176121 : y = (k y (k y y)) ∨ y = (M.op y x) ∨ y = (k y y) := by
    first
    | (have i₁ := eq176090
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq176090
    | exact resolve eq176090 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176090
  have eq176599 : (σ (k (k y y) (k y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq175548 (k y y)
       have i₂ := eq175511
       grind)
    | exact superpose eq175511 eq175548
    | exact resolve eq175548 eq175511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175548
  have eq176689 : (σ (k (k y y) (k y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by grind
  clear eq176599
  have eq176757 : (M.op (M.op (σ y) (σ y)) (σ y)) = (σ (k (k y y) (k y y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq174296 eq176689
    | exact resolve eq176689 eq174296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174296 eq176689
  have eq176825 : (σ y) = (σ (k (k y y) (k y y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq131101 eq176757
    | exact resolve eq176757 eq131101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131101 eq176757
  have eq176908 : (τ (σ y)) = (k (k y y) (k y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k (k y y) (k y y))
       have i₂ := eq176825
       grind)
    | exact superpose eq176825 eq10
    | exact resolve eq10 eq176825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176825
  have eq177490 : y = (k (k y y) (k y y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq176908
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq176908
    | exact resolve eq176908 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176908
  have eq177548 : (k y y) = (M.op (k y y) (k y y)) ∨ y = (M.op y x) ∨ y = (M.op (k y y) (k y y)) := by
    first
    | (have i₁ := eq177490
       have i₂ := eq271 (k y y) (k y y)
       grind)
    | exact superpose eq271 eq177490
    | (have j1 := eq271 (k y y) (k y y)
       grind)
    | exact resolve eq177490 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq184038 : (k y y) ≠ (M.op (k y y) (k y y)) ∨ (k (M.op (k y y) (k y y)) (k y y)) = (M.op (k y y) (M.op (k y y) (k y y))) ∨ y = (M.op y x) ∨ y = (M.op (k y y) (k y y)) := by
    first
    | (have i₁ := eq66 (k y y) (k y y)
       have i₂ := eq177548
       grind)
    | exact superpose eq177548 eq66
    | exact resolve eq66 eq177548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq184070 : (k (M.op (k y y) (k y y)) (k y y)) = (M.op (k y y) (M.op (k y y) (k y y))) ∨ y = (M.op y x) ∨ y = (M.op (k y y) (k y y)) := by
    first
    | (have r₁ := eq184038
       have r₂ := eq177548
       grind)
    | exact resolve eq184038 eq177548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184038
  have eq184076 : (M.op (k y y) (k y y)) = (k (k y y) (k y y)) ∨ y = (M.op y x) ∨ y = (M.op (k y y) (k y y)) := by
    first
    | exact superpose eq177548 eq184070
    | exact resolve eq184070 eq177548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177548 eq184070
  have eq184077 : y = (M.op (k y y) (k y y)) ∨ y = (M.op y x) ∨ y = (M.op (k y y) (k y y)) := by
    first
    | exact superpose eq177490 eq184076
    | exact resolve eq184076 eq177490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177490 eq184076
  have eq184078 : y = (M.op (k y y) (k y y)) ∨ y = (M.op y x) := by grind
  clear eq184077
  have eq184096 : ∀ X0 : G, (k y y) = (M.op y (M.op X0 y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 (k y y) x (k y y)
       have i₂ := eq184078
       grind)
    | exact superpose eq184078 eq9
    | exact resolve eq9 eq184078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184210 : (M.op y x) = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq184096 (M.op x x)
       have i₂ := eq130363
       grind)
    | exact superpose eq130363 eq184096
    | exact resolve eq184096 eq130363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130363 eq184096
  have eq184414 : (M.op (σ y) (σ y)) = (σ (M.op y x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq184210 eq175511
    | exact resolve eq175511 eq184210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175511
  have eq184425 : y = (k y (M.op y x)) ∨ y = (M.op y x) ∨ y = (k y y) := by
    first
    | exact superpose eq184210 eq176121
    | exact resolve eq176121 eq184210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176121
  have eq184429 : y = (M.op (M.op y x) (M.op y x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq184210 eq184078
    | exact resolve eq184078 eq184210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184078
  have eq184483 : y = (k y (M.op y x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq184210 eq184425
    | exact resolve eq184425 eq184210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184210 eq184425
  have eq184484 : y = (k y (M.op y x)) ∨ y = (M.op y x) := by grind
  clear eq184483
  have eq184496 : (σ y) ≠ (σ (M.op y x)) ∨ (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq573 y (M.op y x)
       have i₂ := eq184484
       grind)
    | exact superpose eq184484 eq573
    | (have j0 := eq573 y (M.op y x)
       grind)
    | exact resolve eq573 eq184484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184484
  have eq184516 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq130897 eq184496
    | exact resolve eq184496 eq130897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130897 eq184496
  have eq184518 : (σ y) ≠ (σ (M.op y x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq184516
       have r₂ := eq130354
       grind)
    | exact resolve eq184516 eq130354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184516
  have eq184572 : y = (M.op (M.op y x) (M.op y x)) ∨ y = (M.op y x) := by grind
  clear eq184429
  have eq184577 : ∀ X0 : G, (M.op y x) = (M.op y (M.op X0 y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq130361 y X0
       have i₂ := eq184572
       grind)
    | exact superpose eq184572 eq130361
    | exact resolve eq130361 eq184572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184572
  have eq184942 : (τ (σ (M.op y x))) = (M.op (τ (σ y)) y) ∨ (σ y) = (σ (M.op y x)) ∨ (τ (σ y)) = (M.op (τ (σ y)) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10031 (σ y) y
       have i₂ := eq184414
       grind)
    | exact superpose eq184414 eq10031
    | (have j0 := eq10031 (σ y) y
       grind)
    | exact resolve eq10031 eq184414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10031 eq184414
  have eq185053 : (τ (σ (M.op y x))) = (M.op (τ (σ y)) y) ∨ (τ (σ y)) = (M.op (τ (σ y)) y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq184942
       have r₂ := eq184518
       grind)
    | exact resolve eq184942 eq184518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184518 eq184942
  have eq185113 : (τ (σ (M.op y x))) = (M.op y y) ∨ (τ (σ y)) = (M.op (τ (σ y)) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq185053
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq185053
    | exact resolve eq185053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185053
  have eq185168 : (M.op y x) = (M.op y y) ∨ (τ (σ y)) = (M.op (τ (σ y)) y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq185113
       have i₂ := eq10 (M.op y x)
       grind)
    | exact superpose eq10 eq185113
    | exact resolve eq185113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185113
  have eq185188 : (M.op y x) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq185168
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq185168
    | exact resolve eq185168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185168
  have eq187896 : ∀ X0 : G, y = (M.op (M.op y x) (M.op X0 x)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq130358 X0
       have i₂ := eq185188
       grind)
    | exact superpose eq185188 eq130358
    | exact resolve eq130358 eq185188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187915 : (M.op y x) = (M.op y (M.op y x)) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq184577 y
       have i₂ := eq185188
       grind)
    | exact superpose eq185188 eq184577
    | exact resolve eq184577 eq185188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185188
  have eq188014 : (M.op y x) = (M.op y (M.op y x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq187915
  have eq193004 : x = (M.op (M.op x x) (M.op y x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 x y y
       have i₂ := eq188014
       grind)
    | exact superpose eq188014 eq9
    | exact resolve eq9 eq188014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188014
  have eq193155 : x = (M.op (M.op x x) x) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 x (M.op x x) y
       have i₂ := eq193004
       grind)
    | exact superpose eq193004 eq9
    | exact resolve eq9 eq193004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193156 : ∀ X0 : G, x = (M.op (M.op x x) (M.op X0 x)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq61 x (M.op x x) y x
       have i₂ := eq193004
       grind)
    | exact superpose eq193004 eq61
    | exact resolve eq61 eq193004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq193004
  have eq193261 : y = (M.op (M.op y x) x) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq187896 (M.op x x)
       have i₂ := eq193155
       grind)
    | exact superpose eq193155 eq187896
    | exact resolve eq187896 eq193155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193155
  have eq193314 : y = (M.op (M.op y x) x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq193261
  have eq193368 : y = (M.op (M.op y x) y) ∨ y = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq187896 (M.op y x)
       have i₂ := eq193314
       grind)
    | exact superpose eq193314 eq187896
    | exact resolve eq187896 eq193314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187896 eq193314
  have eq193441 : y = (M.op (M.op y x) y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by grind
  clear eq193368
  have eq193701 : ∀ X0 : G, (M.op x x) = (M.op x (M.op X0 y)) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq130361 x X0
       have i₂ := eq193156 x
       grind)
    | exact superpose eq193156 eq130361
    | exact resolve eq130361 eq193156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193156
  have eq193951 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq193701 (M.op y x)
       have i₂ := eq193441
       grind)
    | exact superpose eq193441 eq193701
    | exact resolve eq193701 eq193441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193441 eq193701
  have eq194034 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op y y) := by grind
  clear eq193951
  have eq194042 : x = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq194034
       have i₂ := eq130331
       grind)
    | exact superpose eq130331 eq194034
    | exact resolve eq194034 eq130331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194034
  have eq194049 : y = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq194042
  have eq194078 : (M.op y x) = (M.op y y) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq184577 y
       have i₂ := eq194049
       grind)
    | exact superpose eq194049 eq184577
    | exact resolve eq184577 eq194049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184577
  have eq194117 : (M.op y x) = (M.op y y) ∨ y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq194078
  have eq194128 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq194049 eq194117
    | exact resolve eq194117 eq194049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194049 eq194117
  have eq194129 : y = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq194128
  have eq194170 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq194129
       grind)
    | exact superpose eq194129 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq194129
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq194129
       grind)
    | exact resolve eq12 eq194129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194129
  have eq194203 : (M.op x y) = (k y x) ∨ x = (M.op x x) := by grind
  clear eq194170
  have eq194216 : x = (k y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq194203
       have i₂ := eq130331
       grind)
    | exact superpose eq130331 eq194203
    | exact resolve eq194203 eq130331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130331 eq194203
  have eq194308 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq573 y x
       have i₂ := eq194216
       grind)
    | exact superpose eq194216 eq573
    | (have j0 := eq573 y x
       grind)
    | exact resolve eq573 eq194216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq194216
  have eq194340 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq194308
  have eq194365 : x = (M.op x x) := by
    first
    | (have r₁ := eq194340
       have r₂ := eq130354
       grind)
    | exact resolve eq194340 eq130354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194340
  have eq194421 : y = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq130358 x
       have i₂ := eq194365
       grind)
    | exact superpose eq194365 eq130358
    | exact resolve eq130358 eq194365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130358
  have eq194443 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq9 x x x
       have i₂ := eq194365
       grind)
    | exact superpose eq194365 eq9
    | exact resolve eq9 eq194365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194444 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq194365
       grind)
    | exact superpose eq194365 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq194365
       grind)
    | exact resolve eq12 eq194365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194365
  have eq194471 : x = (k x x) := by grind
  clear eq194444
  have eq194520 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq661 x x
       have i₂ := eq194471
       grind)
    | exact superpose eq194471 eq661
    | exact resolve eq661 eq194471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq194471
  have eq194540 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq194520
  have eq194590 : ∀ X0 : G, y = (M.op (M.op y y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq130361 (M.op y y) x
       have i₂ := eq194421
       grind)
    | exact superpose eq194421 eq130361
    | exact resolve eq130361 eq194421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130361
  have eq194695 : ∀ X0 : G, x ≠ x ∨ (k x (M.op X0 x)) = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq12 x (M.op X0 x)
       have i₂ := eq194443 X0
       grind)
    | exact superpose eq194443 eq12
    | (have j0 := eq12 x (M.op X0 x)
       grind)
    | (have r₁ := eq12 x (M.op X0 x)
       have r₂ := eq194443 X0
       grind)
    | exact resolve eq12 eq194443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194726 : ∀ X0 : G, (k x (M.op X0 x)) = (M.op (M.op X0 x) x) := by
    intro X0
    first
    | (have j0 := eq194695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194695
  have eq194902 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) x (σ x)
       have i₂ := eq194540
       grind)
    | exact superpose eq194540 eq9
    | exact resolve eq9 eq194540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194540
  have eq195102 : ∀ X0 X1 : G, (M.op y y) = (M.op y (M.op X0 (M.op X1 x))) := by
    intro X0 X1
    first
    | (have i₁ := eq130367 y X0 X1
       have i₂ := eq194590 y
       grind)
    | exact superpose eq194590 eq130367
    | exact resolve eq130367 eq194590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130367 eq194590
  have eq195335 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) (M.op X0 (σ x))) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq12 (σ x) (M.op X0 (σ x))
       have i₂ := eq194902 X0
       grind)
    | exact superpose eq194902 eq12
    | (have j0 := eq12 (σ x) (M.op X0 (σ x))
       grind)
    | (have r₁ := eq12 (σ x) (M.op X0 (σ x))
       have r₂ := eq194902 X0
       grind)
    | exact resolve eq12 eq194902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195366 : ∀ X0 : G, (k (σ x) (M.op X0 (σ x))) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | (have j0 := eq195335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195335
  have eq196859 : (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq195102 x x
       have i₂ := eq194443 x
       grind)
    | exact superpose eq194443 eq195102
    | exact resolve eq195102 eq194443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194443 eq195102
  have eq196986 : y = (M.op (M.op y x) x) := by
    first
    | (have i₁ := eq194421
       have i₂ := eq196859
       grind)
    | exact superpose eq196859 eq194421
    | exact resolve eq194421 eq196859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194421 eq196859
  have eq197088 : y = (M.op (M.op y x) x) := by grind
  clear eq196986
  have eq209799 : (k (σ x) (σ (M.op y x))) = (M.op (σ (M.op y x)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq195366 (M.op (σ (M.op y x)) (σ (M.op y x)))
       have i₂ := eq133786
       grind)
    | exact superpose eq133786 eq195366
    | exact resolve eq195366 eq133786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133786 eq195366
  have eq209924 : (M.op (σ (M.op y x)) (σ x)) = (σ (k x (M.op y x))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq209799
       have i₂ := eq15 x (M.op y x)
       grind)
    | exact superpose eq15 eq209799
    | exact resolve eq209799 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209799
  have eq209935 : (M.op (σ (M.op y x)) (σ x)) = (σ (M.op (M.op y x) x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq209924
       have i₂ := eq194726 y
       grind)
    | exact superpose eq194726 eq209924
    | exact resolve eq209924 eq194726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194726 eq209924
  have eq209938 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq209935
       have i₂ := eq197088
       grind)
    | exact superpose eq197088 eq209935
    | exact resolve eq209935 eq197088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197088 eq209935
  have eq228585 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq209938
  have eq228806 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq194902 (σ (M.op y x))
       have i₂ := eq228585
       grind)
    | exact superpose eq228585 eq194902
    | exact resolve eq194902 eq228585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228585
  have eq228902 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq228806
       have r₂ := eq130354
       grind)
    | exact resolve eq228806 eq130354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228806
  have eq228995 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq228902
  have eq229088 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq194902 (σ y)
       have i₂ := eq228995
       grind)
    | exact superpose eq228995 eq194902
    | exact resolve eq194902 eq228995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194902 eq228995
  have eq229142 : False := by grind
  exact eq229142
