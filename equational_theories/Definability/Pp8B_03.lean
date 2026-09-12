import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1242`: `x = x ◇ (((y ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_y_pxy_Equation1242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1242 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1242.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq267 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq267 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267
  have eq275 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq274 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq379 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq275 X1 X0
       grind)
    | exact superpose eq275 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq275 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq275 X0 X1
       grind)
    | exact resolve eq13 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq275 (σ x) (σ y)
       grind)
    | exact superpose eq275 eq16
    | (have j1 := eq275 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq379 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq390 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq385
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq385
    | exact resolve eq385 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq392 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq389 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq389 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq389 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq417 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq392 X1 (τ X0)
       grind)
    | exact superpose eq392 eq17
    | (have j1 := eq392 X1 (τ X0)
       grind)
    | exact resolve eq17 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq423 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq392 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq417 X1 (τ X0)
       grind)
    | exact superpose eq417 eq18
    | (have j1 := eq417 X1 (τ X0)
       grind)
    | exact resolve eq18 eq417
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq417
  have eq621 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq616
    | (have j0 := eq616 X0 X1
       grind)
    | exact resolve eq616 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq637 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq621 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq621
    | (have j0 := eq621 X0 X1
       grind)
    | exact resolve eq621 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq640 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq637 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq637
    | (have j0 := eq637 X0 X1
       grind)
    | exact resolve eq637 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq734 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq640 X0 X1
       have i₂ := eq392 X0 X1
       grind)
    | exact superpose eq392 eq640
    | (have j0 := eq640 X1 X0
       have j1 := eq392 X1 X0
       grind)
    | exact resolve eq640 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq640
  have eq793 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq734 X0 X1
       have j1 := eq423 X0 X1
       grind)
    | (have r₁ := eq734 X0 X1
       have r₂ := eq423 X0 X1
       grind)
    | exact resolve eq734 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423 eq734
  have eq834 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq793 X1 (σ X0)
       grind)
    | exact superpose eq793 eq22
    | (have j1 := eq793 X1 (σ X0)
       grind)
    | exact resolve eq22 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq793
  have eq867 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq834 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq834
    | (have j0 := eq834 X0 X1
       grind)
    | exact resolve eq834 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq887 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq867 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq867
    | (have j0 := eq867 X0 X1
       grind)
    | exact resolve eq867 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq867
  have eq1163 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq887 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq887
    | exact resolve eq887 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq1225 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1163 x y
       grind)
    | exact superpose eq1163 eq16
    | (have j1 := eq1163 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1163 x y
       grind)
    | exact resolve eq16 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1240 : y = (k x y) := by grind
  clear eq1225
  have eq1845 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq390
       have i₂ := eq275 x y
       grind)
    | exact superpose eq275 eq390
    | (have j1 := eq275 x y
       grind)
    | exact resolve eq390 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1848 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1845
  have eq1849 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1848
       have i₂ := eq1240
       grind)
    | exact superpose eq1240 eq1848
    | exact resolve eq1848 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq1850 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1849
       have i₂ := eq1240
       grind)
    | exact superpose eq1240 eq1849
    | exact resolve eq1849 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849
  have eq1851 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq390
       have i₂ := eq1850
       grind)
    | exact superpose eq1850 eq390
    | exact resolve eq390 eq1850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq1850
  have eq1865 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1851
  have eq1866 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1865
       have i₂ := eq1240
       grind)
    | exact superpose eq1240 eq1865
    | exact resolve eq1865 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1865
  have eq1867 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1866
  have eq1870 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1867
       grind)
    | exact superpose eq1867 eq16
    | exact resolve eq16 eq1867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867
  have eq1909 : (σ y) ≠ (σ y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1870
       have i₂ := eq275 x y
       grind)
    | exact superpose eq275 eq1870
    | (have j1 := eq275 x y
       grind)
    | exact resolve eq1870 eq275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq1912 : (M.op x y) = (k x y) := by grind
  clear eq1909
  have eq1914 : y = (M.op x y) := by
    first
    | (have i₁ := eq1912
       have i₂ := eq1240
       grind)
    | exact superpose eq1240 eq1912
    | exact resolve eq1912 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240 eq1912
  have eq1915 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1870
       have i₂ := eq1914
       grind)
    | exact superpose eq1914 eq1870
    | exact resolve eq1870 eq1914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870 eq1914
  have eq1931 : False := by grind
  exact eq1931

/-- `Equation1255`: `x = x ◇ (((y ◇ y) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation1255 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1255 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1255.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq67 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1
       have i₂ := eq77 X1
       grind)
    | exact superpose eq77 eq95
    | (have j0 := eq95 X0 X1
       grind)
    | exact resolve eq95 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq126 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq400 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq101 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq101 X0 X1
       grind)
    | exact superpose eq101 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq101 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq101 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq101 X0 X1
       grind)
    | exact resolve eq13 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq404 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq400 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq408 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq404 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq404 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq404 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404
  have eq418 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq408 X0 X1
       have j1 := eq126 X1 (σ X0)
       grind)
    | (have r₁ := eq408 X0 X0
       have r₂ := eq126 X0 X1
       grind)
    | exact resolve eq408 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq408
  have eq425 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq418 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq418
    | (have j0 := eq418 X0 X1
       grind)
    | exact resolve eq418 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq426 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq432 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq426 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq426
    | exact resolve eq426 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq426 x y
       grind)
    | exact superpose eq426 eq16
    | exact resolve eq16 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq562 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq432 X0 (τ X1)
       grind)
    | exact superpose eq432 eq18
    | exact resolve eq18 eq432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq432
  have eq575 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq562 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq562
    | exact resolve eq562 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq587 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq575 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq575
    | exact resolve eq575 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq669 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq443
       have i₂ := eq587 x y
       grind)
    | exact superpose eq587 eq443
    | exact resolve eq443 eq587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443 eq587
  have eq670 : False := by grind
  exact eq670

/-- `Equation1255`: `x = x ◇ (((y ◇ y) ◇ z) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation1255 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1255 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1255.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  have eq70 : y ≠ (M.op x y) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq87 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq85
    | exact resolve eq85 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq88 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87
    | exact resolve eq87 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq962 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq963 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq962
    | exact resolve eq962 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq966 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq963
       have r₂ := eq28
       grind)
    | exact resolve eq963 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963
  have eq968 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq966
    | exact resolve eq966 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq970 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq968 eq71
    | (have r₁ := eq71
       have r₂ := eq968
       grind)
    | exact resolve eq71 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq971 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq968 eq28
    | exact resolve eq28 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq972 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq970
  have eq973 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq972
  have eq1066 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq973 eq88
    | exact resolve eq88 eq973
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq973
  have eq1070 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1066
  have eq1075 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1070
       have r₂ := eq971
       grind)
    | exact resolve eq1070 eq971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971 eq1070
  have eq1160 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1075 eq30
    | exact resolve eq30 eq1075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1075
  have eq1178 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1160
    | exact resolve eq1160 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1179 : y = (M.op x y) ∨ x = y := by grind
  clear eq1178
  have eq1182 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1179 eq21
    | exact resolve eq21 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1184 : y ≠ y ∨ x = y ∨ y = (k x y) ∨ x = y := by
    first
    | exact superpose eq1179 eq70
    | (have r₁ := eq70
       have r₂ := eq1179
       grind)
    | exact resolve eq70 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq1179
  have eq1192 : y ≠ y ∨ x = y ∨ y = (k x y) := by grind
  clear eq1184
  have eq1193 : y = (k x y) ∨ x = y := by grind
  clear eq1192
  have eq1202 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1182
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1182
    | exact resolve eq1182 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1182
  have eq1236 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq1193
       grind)
    | exact superpose eq1193 eq49
    | exact resolve eq49 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1193
  have eq1241 : (σ y) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1236
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1236
    | exact resolve eq1236 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236
  have eq1250 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1241 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq1241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1251 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1250
  have eq1257 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq1251
    | exact resolve eq1251 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251
  have eq1373 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1257 eq28
    | exact resolve eq28 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1257
  have eq1376 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1373
       have r₂ := eq1202
       grind)
    | exact resolve eq1373 eq1202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202 eq1373
  have eq1379 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1376 eq30
    | exact resolve eq30 eq1376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1376
  have eq1402 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1379
    | exact resolve eq1379 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1379
  have eq1403 : x = y := by grind
  clear eq1402
  have eq1406 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1403
       grind)
    | exact superpose eq1403 eq19
    | exact resolve eq19 eq1403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1407 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1403
       grind)
    | exact superpose eq1403 eq25
    | exact resolve eq25 eq1403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1403
  have eq1426 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1407
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1407
    | exact resolve eq1407 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1407
  have eq1491 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1426 eq27
    | exact resolve eq27 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1426
  have eq1529 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1491 eq69
    | exact resolve eq69 eq1491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq1491
  have eq1538 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1529
       have i₂ := eq1406
       grind)
    | exact superpose eq1406 eq1529
    | exact resolve eq1529 eq1406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406 eq1529
  have eq1624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1538 eq15
    | exact resolve eq15 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq1655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1624
    | exact resolve eq1624 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1624
  have eq1661 : False := by grind
  exact eq1661

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then X else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_x_x_x_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
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
  clear eq45
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
  have eq175 : x ≠ (M.op x y) ∨ x = (k x y) := by
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
  have eq177 : y ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq178 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq530 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x y) X0) y)) = X0 := by
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
  have eq531 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have r₂ := eq16 X0 X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq535 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq547 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq531 eq16
    | exact resolve eq16 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq644 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq744 : ∀ X0 X1 : G, (τ (σ x)) = (k x (τ (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq91 (M.op (M.op (M.op X1 x) sF2) x)
       have i₂ := eq536 sF2 X1 x
       grind)
    | exact superpose eq536 eq91
    | exact resolve eq91 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq536
  have eq747 : ∀ X0 X1 : G, x = (k x (τ (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq30 eq744
    | exact resolve eq744 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq744
  have eq1169 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq643
       grind)
    | exact superpose eq643 eq40
    | exact resolve eq40 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1170 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1169
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1169
    | exact resolve eq1169 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq1172 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq1170
    | exact resolve eq1170 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1170
  have eq1759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1172 eq644
    | exact resolve eq644 eq1172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1768 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1759
       have r₂ := eq27
       grind)
    | exact resolve eq1759 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq1774 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1768 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1768
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1768
       grind)
    | exact resolve eq13 eq1768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1768
  have eq1791 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq1774
  have eq1798 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1791
       have r₂ := eq178
       grind)
    | exact resolve eq1791 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq1791
  have eq1815 : (τ (σ y)) = (k (τ (σ y)) x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1798 eq142
    | exact resolve eq142 eq1798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq1798
  have eq1823 : y = (k y x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq32 eq1815
    | exact resolve eq1815 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815
  have eq1826 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1823
       have r₂ := eq177
       grind)
    | exact resolve eq1823 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1823
  have eq1829 : y = (k y x) := by
    first
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq1826
       have r₂ := eq13 y x
       grind)
    | exact resolve eq1826 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1826
  have eq1833 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq643
       have i₂ := eq1829
       grind)
    | exact superpose eq1829 eq643
    | exact resolve eq643 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq1835 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1829
       grind)
    | exact superpose eq1829 eq40
    | exact resolve eq40 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1829
  have eq1838 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1833
  have eq1841 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq1835
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1835
    | exact resolve eq1835 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835
  have eq1847 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1841 eq644
    | exact resolve eq644 eq1841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq1841
  have eq1853 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1847
  have eq1869 : x = (M.op x (M.op y (M.op (M.op (M.op (σ x) (σ y)) y) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq547 y x
       have i₂ := eq1838
       grind)
    | exact superpose eq1838 eq547
    | exact resolve eq547 eq1838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq1883 : x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq531 eq1869
    | exact resolve eq1869 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq1889 : y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq1896 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1889
       grind)
    | exact superpose eq1889 eq18
    | exact resolve eq18 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1897 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1889
       grind)
    | exact superpose eq1889 eq24
    | exact resolve eq24 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq1938 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1897
    | exact resolve eq1897 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897
  have eq1984 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1853 eq547
    | exact resolve eq547 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq1988 : x = (k x (τ (M.op (M.op (σ y) (σ x)) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1853 eq747
    | exact resolve eq747 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq747
  have eq1995 : x = (k x (τ (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1853 eq1988
    | exact resolve eq1988 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988
  have eq1998 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq531 eq1984
    | exact resolve eq1984 eq531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1984
  have eq2003 : x = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1853 eq1995
    | exact resolve eq1995 eq1853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1853 eq1995
  have eq2004 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1998
    | exact resolve eq1998 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1998
  have eq2010 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq2003
    | exact resolve eq2003 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq2003
  have eq2011 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2004 eq27
    | exact resolve eq27 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2014 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) X0) (σ y))) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2004 eq531
    | exact resolve eq531 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq2044 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1938 eq2011
    | (have r₁ := eq2011
       have r₂ := eq1938
       grind)
    | exact resolve eq2011 eq1938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2045 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2044
  have eq2214 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2045 eq27
    | exact resolve eq27 eq2045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2272 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1938 eq2214
    | exact resolve eq2214 eq1938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938 eq2214
  have eq2273 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq2272
  have eq2446 : x ≠ x ∨ x = (M.op y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq682 y x
       have i₂ := eq2010
       grind)
    | exact superpose eq2010 eq682
    | (have j0 := eq682 y x
       grind)
    | (have r₁ := eq682 y x
       have r₂ := eq2010
       grind)
    | exact resolve eq682 eq2010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2447 : x = (M.op y x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2446
  have eq2448 : x = (M.op x y) ∨ x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2447
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2447
    | exact resolve eq2447 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447
  have eq2453 : x = (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1889 eq2448
    | exact resolve eq2448 eq1889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1889 eq2448
  have eq2457 : x = (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2045 eq2453
    | exact resolve eq2453 eq2045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045 eq2453
  have eq2459 : x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2457
       have r₂ := eq2273
       grind)
    | exact resolve eq2457 eq2273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273 eq2457
  have eq2480 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2459 eq530
    | exact resolve eq530 eq2459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq2459
  have eq2509 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2480
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2480
    | exact resolve eq2480 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2480
  have eq2520 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1896 eq2509
    | exact resolve eq2509 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1896 eq2509
  have eq2521 : x = (M.op x y) := by grind
  clear eq2520
  have eq2529 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq2521
       grind)
    | exact superpose eq2521 eq22
    | exact resolve eq22 eq2521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2532 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) y) := by
    first
    | (have i₁ := eq175
       have i₂ := eq2521
       grind)
    | exact superpose eq2521 eq175
    | (have r₁ := eq175
       have r₂ := eq2521
       grind)
    | exact resolve eq175 eq2521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2521
  have eq2554 : (M.op x y) = (k (M.op x y) y) := by grind
  clear eq2532
  have eq2564 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2529 eq20
    | exact resolve eq20 eq2529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2529
  have eq2697 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2554 eq41
    | exact resolve eq41 eq2554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2554
  have eq2702 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq2697
    | exact resolve eq2697 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2697
  have eq2704 : (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2564 eq2702
    | exact resolve eq2702 eq2564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2702
  have eq2772 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2704 eq682
    | (have j0 := eq682 (σ y) (σ x)
       grind)
    | (have r₁ := eq682 (σ y) (σ x)
       have r₂ := eq2704
       grind)
    | exact resolve eq682 eq2704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq2704
  have eq2773 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2772
  have eq2774 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq2773
    | exact resolve eq2773 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2773
  have eq5017 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2774 eq2014
    | exact resolve eq2014 eq2774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2014 eq2774
  have eq5088 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5017
  have eq5116 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5088
    | exact resolve eq5088 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088
  have eq5122 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2004 eq5116
    | exact resolve eq5116 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004 eq5116
  have eq5125 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5122
    | exact resolve eq5122 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq5122
  have eq5126 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5125
  have eq5131 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5126 eq27
    | exact resolve eq27 eq5126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5126
  have eq5179 : False := by grind
  exact eq5179

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pxy_x_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X1 X2) X0) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq107 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
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
  have eq124 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq107 X0 X1 X2 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq107
    | exact resolve eq107 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq513 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ x) (σ y)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op (M.op X2 X3) X0) X3))) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq545 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq544 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq549 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq545 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq545 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq545 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545
  have eq551 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq517
    | (have j0 := eq517 X0 X1 x x
       grind)
    | exact resolve eq517 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq552 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq551 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq553 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq513
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq513
    | exact resolve eq513 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513
  have eq564 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq549 (σ X0)
       grind)
    | exact superpose eq549 eq15
    | exact resolve eq15 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq564 X0
       have i₂ := eq549 X0
       grind)
    | exact superpose eq549 eq564
    | exact resolve eq564 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq673 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq552 X0 X1
       grind)
    | exact superpose eq552 eq12
    | (have j1 := eq552 X1 X0
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq552 X0 X1
       grind)
    | exact resolve eq12 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (M.op (M.op X2 X3) X0) X3))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq552 X1 X0
       grind)
    | exact superpose eq552 eq61
    | (have j1 := eq552 (M.op X0 (M.op (M.op (M.op X2 X3) X0) X3)) X1
       grind)
    | exact resolve eq61 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 X1 X2 X3 : G, (k X1 (M.op X0 (M.op (M.op (M.op X2 X3) X0) X3))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq65 X0 X1 X2 X3
       have i₂ := eq552 X1 X0
       grind)
    | exact superpose eq552 eq65
    | (have j1 := eq552 X1 X0
       grind)
    | exact resolve eq65 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq702 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq552 (σ y) (σ x)
       grind)
    | exact superpose eq552 eq16
    | (have j1 := eq552 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq706 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq673 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq707 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq702
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq702
    | exact resolve eq702 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq708 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq678 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq678
    | (have j0 := eq678 X0 X1 x x
       grind)
    | exact resolve eq678 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq709 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq675 X0 X1 x x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq675
    | (have j0 := eq675 X0 X1 x x
       grind)
    | exact resolve eq675 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq746 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq706 X0 (τ X1)
       grind)
    | exact superpose eq706 eq17
    | (have j1 := eq706 X0 (τ X1)
       grind)
    | exact resolve eq17 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq706
  have eq778 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq708 (σ X0) X1
       grind)
    | exact superpose eq708 eq22
    | (have j1 := eq708 (σ X0) X1
       grind)
    | exact resolve eq22 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq708 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq709 (σ X0) X1
       grind)
    | exact superpose eq709 eq22
    | (have j1 := eq709 (σ X0) X1
       grind)
    | exact resolve eq22 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1836 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq746 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq746
    | exact resolve eq746 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq746
  have eq1877 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1836 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1836
    | (have j0 := eq1836 X0 X1
       grind)
    | exact resolve eq1836 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1836
  have eq2264 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq778 X1 (σ X0)
       grind)
    | exact superpose eq778 eq28
    | (have j1 := eq778 X1 (σ X0)
       grind)
    | exact resolve eq28 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778
  have eq2275 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2264 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq2264
    | (have j0 := eq2264 X0 X1
       grind)
    | exact resolve eq2264 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2264
  have eq2287 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2275 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2275
    | (have j0 := eq2275 X0 X1
       grind)
    | exact resolve eq2275 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2275
  have eq2294 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2287 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2287
    | (have j0 := eq2287 X0 X1
       grind)
    | exact resolve eq2287 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2287
  have eq2374 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) (σ X0))
       have i₂ := eq2294 X0 X1
       grind)
    | exact superpose eq2294 eq11
    | (have j1 := eq2294 X0 X1
       grind)
    | exact resolve eq11 eq2294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2294
  have eq2425 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2374 y x
       grind)
    | exact superpose eq2374 eq16
    | (have j1 := eq2374 y x
       grind)
    | exact resolve eq16 eq2374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq2494 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2425
       have i₂ := eq709 x y
       grind)
    | exact superpose eq709 eq2425
    | (have j1 := eq709 x y
       grind)
    | exact resolve eq2425 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2495 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq2425
       have i₂ := eq708 x y
       grind)
    | exact superpose eq708 eq2425
    | (have j1 := eq708 x y
       grind)
    | exact resolve eq2425 eq708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq2425
  have eq2501 : y = (M.op x y) ∨ y = (k y x) := by grind
  clear eq2495
  have eq2502 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq2494
  have eq2503 : y = (k y x) := by
    first
    | (have j1 := eq800 y x
       grind)
    | (have r₁ := eq2501
       have r₂ := eq800 y x
       grind)
    | exact resolve eq2501 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800 eq2501
  have eq2598 : ∀ X0 X1 : G, x = (M.op x (M.op y (M.op (M.op (M.op X0 X1) y) X1))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq61 y x X0 X1
       have i₂ := eq2502
       grind)
    | exact superpose eq2502 eq61
    | exact resolve eq61 eq2502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502
  have eq2613 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2598 x x
       have i₂ := eq9 y x x
       grind)
    | exact superpose eq9 eq2598
    | exact resolve eq2598 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq6876 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X0 X1) X2
       have i₂ := eq124 X2 X0 X1
       grind)
    | exact superpose eq124 eq9
    | exact resolve eq9 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq7188 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X0 X1 x (M.op X0 X1)
       have i₂ := eq6876 x (M.op X0 X1) X0
       grind)
    | exact superpose eq6876 eq65
    | exact resolve eq65 eq6876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq7189 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1 x (M.op X0 X1)
       have i₂ := eq6876 x (M.op X0 X1) X0
       grind)
    | exact superpose eq6876 eq61
    | exact resolve eq61 eq6876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq6876
  have eq7282 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 (σ X0))
       have i₂ := eq7188 X1 (σ X0)
       grind)
    | exact superpose eq7188 eq28
    | exact resolve eq28 eq7188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq7290 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7282 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7282
    | exact resolve eq7282 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7282
  have eq7321 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7189 X0 (M.op X1 X0)
       have i₂ := eq7189 X1 X0
       grind)
    | exact superpose eq7189 eq7189
    | exact resolve eq7189 eq7189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7327 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq7189 (σ X0) (σ X0)
       have i₂ := eq583 X0
       grind)
    | exact superpose eq583 eq7189
    | exact resolve eq7189 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq7356 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X0 (M.op X2 X0)
       have i₂ := eq7189 X2 X0
       grind)
    | exact superpose eq7189 eq9
    | exact resolve eq9 eq7189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7380 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7188 X0 (M.op X1 X0)
       have i₂ := eq7189 X1 X0
       grind)
    | exact superpose eq7189 eq7188
    | exact resolve eq7188 eq7189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7188
  have eq7557 : ∀ X0 X1 : G, (k X0 (k (τ (σ X0)) X1)) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7290 X0 (σ X1)
       have i₂ := eq888 X1 (σ X0)
       grind)
    | exact superpose eq888 eq7290
    | (have j1 := eq888 X1 (σ X0)
       grind)
    | exact resolve eq7290 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq7290
  have eq7601 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7557 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7557
    | (have j0 := eq7557 X0 X1
       grind)
    | exact resolve eq7557 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7557
  have eq7797 : ∀ X0 X1 : G, (τ (M.op X0 (σ X1))) = (k (τ (M.op X0 (σ X1))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X0 (σ X1)) X1
       have i₂ := eq7380 (σ X1) X0
       grind)
    | exact superpose eq7380 eq22
    | exact resolve eq22 eq7380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7380
  have eq7874 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ X0) X1) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq7327 X0
       grind)
    | exact superpose eq7327 eq9
    | exact resolve eq9 eq7327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7327
  have eq8173 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7356 x y X0
       have i₂ := eq2613
       grind)
    | exact superpose eq2613 eq7356
    | exact resolve eq7356 eq2613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613 eq7356
  have eq10577 : ∀ X0 X1 : G, (τ X0) = (k (τ X0) X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7797 X1 X1
       have i₂ := eq552 (σ X1) X1
       grind)
    | exact superpose eq552 eq7797
    | (have j1 := eq552 (σ X1) X0
       grind)
    | exact resolve eq7797 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7797
  have eq20791 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k X0 (k X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7189 (σ X0) (σ X1)
       have i₂ := eq7601 X0 X1
       grind)
    | exact superpose eq7601 eq7189
    | (have j1 := eq7601 X1 X0
       grind)
    | exact resolve eq7189 eq7601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7601
  have eq33594 : (σ (M.op x y)) ≠ (σ x) ∨ y = (k y (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20791 y x
       grind)
    | exact superpose eq20791 eq16
    | (have j1 := eq20791 y x
       grind)
    | exact resolve eq16 eq20791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20791
  have eq33810 : y = (k y y) ∨ (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq33594
       have i₂ := eq2503
       grind)
    | exact superpose eq2503 eq33594
    | exact resolve eq33594 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33594
  have eq33855 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq33810
       have i₂ := eq549 y
       grind)
    | exact superpose eq549 eq33810
    | exact resolve eq33810 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq33810
  have eq33909 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq33855
       have i₂ := eq552 y x
       grind)
    | exact superpose eq552 eq33855
    | (have j1 := eq552 y y
       grind)
    | exact resolve eq33855 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552 eq33855
  have eq33916 : y = (M.op y y) ∨ (M.op x y) = (k y x) := by grind
  clear eq33909
  have eq33924 : y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq33916
       have i₂ := eq2503
       grind)
    | exact superpose eq2503 eq33916
    | exact resolve eq33916 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33916
  have eq33989 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7321 y x
       have i₂ := eq33924
       grind)
    | exact superpose eq33924 eq7321
    | exact resolve eq7321 eq33924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7321 eq33924
  have eq34009 : y = (M.op y y) := by grind
  clear eq33989
  have eq34049 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) X0) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq7874 y X0
       have i₂ := eq34009
       grind)
    | exact superpose eq34009 eq7874
    | exact resolve eq7874 eq34009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7874 eq34009
  have eq56030 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10577 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq10577
    | (have j0 := eq10577 (σ X0) X1
       grind)
    | exact resolve eq10577 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10577
  have eq56151 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56030 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq56030
    | (have j0 := eq56030 X0 X1
       grind)
    | exact resolve eq56030 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56030
  have eq56662 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq56151 x y
       grind)
    | exact superpose eq56151 eq16
    | (have j1 := eq56151 x y
       grind)
    | exact resolve eq16 eq56151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56151
  have eq56898 : x = (k x y) := by
    first
    | (have j1 := eq1877 y x
       grind)
    | (have r₁ := eq56662
       have r₂ := eq1877 y x
       grind)
    | exact resolve eq56662 eq1877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1877 eq56662
  have eq56992 : x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq709 y x
       have i₂ := eq56898
       grind)
    | exact superpose eq56898 eq709
    | (have j0 := eq709 y x
       grind)
    | exact resolve eq709 eq56898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq57076 : y = (M.op y (M.op y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8173 y
       have i₂ := eq56992
       grind)
    | exact superpose eq56992 eq8173
    | exact resolve eq8173 eq56992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8173
  have eq57168 : y = (M.op y (M.op y x)) ∨ x = (M.op x y) := by grind
  clear eq57076
  have eq61402 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq57168
       have i₂ := eq56992
       grind)
    | exact superpose eq56992 eq57168
    | exact resolve eq57168 eq56992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56992 eq57168
  have eq61521 : x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq61402
  have eq61661 : y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq7189 x y
       have i₂ := eq61521
       grind)
    | exact superpose eq61521 eq7189
    | exact resolve eq7189 eq61521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61521
  have eq61694 : y = (M.op y x) := by grind
  clear eq61661
  have eq61806 : x = (M.op x y) := by
    first
    | (have i₁ := eq7189 y x
       have i₂ := eq61694
       grind)
    | exact superpose eq61694 eq7189
    | exact resolve eq7189 eq61694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61694
  have eq61898 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq553
       have i₂ := eq61806
       grind)
    | exact superpose eq61806 eq553
    | exact resolve eq553 eq61806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq62016 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq61898
  have eq62051 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq62016
       have i₂ := eq56898
       grind)
    | exact superpose eq56898 eq62016
    | exact resolve eq62016 eq56898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56898 eq62016
  have eq164596 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7189 (σ y) (σ x)
       have i₂ := eq62051
       grind)
    | exact superpose eq62051 eq7189
    | exact resolve eq7189 eq62051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62051
  have eq173794 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq164596
       grind)
    | exact superpose eq164596 eq16
    | exact resolve eq16 eq164596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164596
  have eq174044 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq173794
       have i₂ := eq61806
       grind)
    | exact superpose eq61806 eq173794
    | exact resolve eq173794 eq61806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173794
  have eq174045 : (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq174044
  have eq174111 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq34049 (σ x)
       have i₂ := eq174045
       grind)
    | exact superpose eq174045 eq34049
    | exact resolve eq34049 eq174045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34049
  have eq174576 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq7189 (σ x) (M.op (σ x) (σ y))
       have i₂ := eq174111
       grind)
    | exact superpose eq174111 eq7189
    | exact resolve eq7189 eq174111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7189 eq174111
  have eq189811 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq707
       have i₂ := eq61806
       grind)
    | exact superpose eq61806 eq707
    | exact resolve eq707 eq61806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq189825 : (M.op (σ x) (σ y)) = (σ (k y x)) := by grind
  clear eq189811
  have eq189852 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq189825
       have i₂ := eq2503
       grind)
    | exact superpose eq2503 eq189825
    | exact resolve eq189825 eq2503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2503 eq189825
  have eq189884 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq189852
       grind)
    | exact superpose eq189852 eq16
    | exact resolve eq16 eq189852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189896 : (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq174576
       have i₂ := eq189852
       grind)
    | exact superpose eq189852 eq174576
    | exact resolve eq174576 eq189852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174576 eq189852
  have eq190150 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq189896
       have i₂ := eq174045
       grind)
    | exact superpose eq174045 eq189896
    | exact resolve eq189896 eq174045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174045 eq189896
  have eq190154 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq189884
       have i₂ := eq61806
       grind)
    | exact superpose eq61806 eq189884
    | exact resolve eq189884 eq61806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61806 eq189884
  have eq190197 : False := by grind
  exact eq190197

/-- `Equation1260`: `x = x ◇ (((y ◇ z) ◇ x) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxy_pxx_pyx_Equation1260 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1260 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1260.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op x y) X0) y)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 X0 (M.op (M.op (M.op X2 X3) X0) X3)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X3) = (M.op (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X3) (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X3) X0 X1
       have i₂ := eq14 (M.op X0 X1) X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op (M.op (M.op X1 X2) X0) X2) X0) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X1 X2) X0) X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op (M.op X1 X2) X0) X2) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X1 X2) X0) X2) X0
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (k (M.op (M.op (M.op X1 X2) X0) X2) X0) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq65 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq69 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq77 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq92 : (σ (k x (k y x))) = (k (σ x) (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq35 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq35
    | exact resolve eq35 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq113 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k y x) = (M.op y y) := by
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
  have eq114 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq172 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq39
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq39 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq214 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op (M.op (M.op X1 x) sF4) x)
       have i₂ := eq14 sF4 X1 x
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : ∀ X0 : G, X0 ≠ X0 ∨ (k (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq51 eq13
    | (have j0 := eq13 (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0
       have r₂ := eq51 X0
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 : G, (k (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0) := by
    intro X0
    first
    | (have j0 := eq220 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq590 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq590
    | exact resolve eq590 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq594 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq591
       have r₂ := eq27
       grind)
    | exact resolve eq591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq596 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq594
    | exact resolve eq594 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq598 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq596
    | exact resolve eq596 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596
  have eq600 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq598 eq114
    | (have r₁ := eq114
       have r₂ := eq598
       grind)
    | exact resolve eq114 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq603 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq598 eq27
    | exact resolve eq27 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  have eq605 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq600
  have eq607 : ∀ X0 X1 : G, y = (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0 X1
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) X1))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) = (M.op (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) (M.op X0 (M.op (M.op (M.op X4 X5) X0) X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X0 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X4 X5
       have i₂ := eq52 X1 X0 X2 X3
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq610 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) (M.op X0 (M.op (M.op (M.op X3 X4) X0) X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 X0 (M.op (M.op (M.op X1 X2) X0) X2) X3 X4
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) y) = (M.op (M.op (M.op (M.op x y) X0) y) (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) (M.op X0 (M.op (M.op (M.op X1 X2) X0) X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq52
    | exact resolve eq52 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op (M.op X3 X0) (M.op (M.op (M.op X4 X5) X3) X5))))) = X1 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X2 X1 X0 (M.op (M.op X3 X0) (M.op (M.op (M.op X4 X5) X3) X5))
       have i₂ := eq52 X3 X0 X4 X5
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X2 (M.op (M.op (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op (M.op X4 X5) X3) X5)) X2) (M.op (M.op X0 X1) X1))) = X2 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op (M.op X4 X5) X3) X5)) X2 X0 X1
       have i₂ := eq52 X3 (M.op X0 X1) X4 X5
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op (M.op (M.op (M.op X3 X4) (M.op X0 X1)) X4) X2) (M.op (M.op X0 X1) X1))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op (M.op (M.op X3 X4) (M.op X0 X1)) X4) X2 X0 X1
       have i₂ := eq14 (M.op X0 X1) X3 X4
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) = (M.op (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0
       have i₂ := eq52 X1 X0 X2 X3
       grind)
    | exact superpose eq52 eq13
    | (have j0 := eq13 (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X0 X1) (M.op (M.op (M.op X2 X3) X0) X3)) X1
       have r₂ := eq52 X0 X1 X2 X3
       grind)
    | exact resolve eq13 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 X1 X2 X3 : G, (k (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) = (M.op (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq623 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq629 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq612 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq612
    | exact resolve eq612 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq630 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) y) = (M.op (M.op (M.op (M.op x y) X0) y) X0) := by
    intro X0
    first
    | (have i₁ := eq611 X0 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq611
    | exact resolve eq611 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq631 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = (M.op (M.op (M.op (M.op X1 X2) X0) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq610 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq610
    | exact resolve eq610 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq632 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) = (M.op (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq609 X0 X1 X2 X3 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq609
    | exact resolve eq609 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq609
  have eq637 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) y)) X1) = (M.op (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq50 eq66
    | exact resolve eq66 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq665 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq605
       have r₂ := eq604
       grind)
    | exact resolve eq605 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq605
  have eq695 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op X5 X4) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X1) X5) (M.op (M.op X2 X3) X3)))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 X5 X4 (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X1) (M.op (M.op X2 X3) X3)
       have i₂ := eq53 X2 X3 X0 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq53
  have eq706 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq665 eq99
    | exact resolve eq99 eq665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq709 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq706
  have eq769 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq906 : y = (M.op y (M.op (M.op x y) (M.op (M.op (M.op x y) x) y))) := by
    first
    | (have i₁ := eq214 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq214
    | (have j0 := eq214 x y
       grind)
    | exact resolve eq214 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq907 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op x y) (σ x)) y))) := by
    first
    | exact superpose eq26 eq214
    | (have j0 := eq214 (σ x) (σ y)
       grind)
    | exact resolve eq214 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq1223 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq709 eq608
    | exact resolve eq608 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq1304 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) := by
    intro X0
    first
    | exact superpose eq629 eq14
    | exact resolve eq14 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1363 : ∀ X0 : G, y = (M.op y (M.op (M.op (M.op x y) X0) y)) := by
    intro X0
    first
    | exact superpose eq630 eq14
    | exact resolve eq14 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq2860 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) = (k (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq629 eq224
    | exact resolve eq224 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq629
  have eq4325 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq598 eq1223
    | exact resolve eq1223 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq598 eq1223
  have eq4348 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4325
  have eq4356 : (σ y) = (M.op (σ y) (M.op (σ y) (M.op (M.op (σ (M.op x y)) (σ x)) (σ y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4348
       have r₂ := eq604
       grind)
    | exact resolve eq4348 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq4348
  have eq4503 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op (M.op X0 X1) X1) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq51 eq631
    | exact resolve eq631 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq4506 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X1) = (M.op (M.op (M.op (M.op X0 X1) X2) X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq631 X2 (M.op X1 X2) X0
       have i₂ := eq631 X0 X1 X2
       grind)
    | exact superpose eq631 eq631
    | exact resolve eq631 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4509 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X0 X1) X2
       have i₂ := eq631 X2 X0 X1
       grind)
    | exact superpose eq631 eq14
    | exact resolve eq14 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9641 : (σ (k x (k y x))) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq77 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq77
    | exact resolve eq77 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq10278 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq172 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172
  have eq11746 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X3 (M.op (M.op X4 X3) (M.op (M.op X5 X4) (M.op (M.op X6 X5) (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X1) X6) X2))))) = X3 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq615 X5 X3 X4 X6 (M.op (M.op (M.op X0 X1) X2) X1) X2
       have i₂ := eq631 X2 X0 X1
       grind)
    | exact superpose eq631 eq615
    | exact resolve eq615 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq631
  have eq12503 : ∀ X0 X1 : G, (k (M.op y (M.op (M.op (M.op x y) y) y)) (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) = (M.op (M.op y (M.op (M.op (M.op x y) y) y)) (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | exact superpose eq607 eq637
    | exact resolve eq637 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637
  have eq12669 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) = (k y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | exact superpose eq50 eq12503
    | exact resolve eq12503 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12503
  have eq12744 : ∀ X0 X1 : G, y = (k y (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | exact superpose eq607 eq12669
    | exact resolve eq12669 eq607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq607 eq12669
  have eq14720 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq769 x y
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq769
    | (have j0 := eq769 x y
       grind)
    | exact resolve eq769 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq14763 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14720
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14720
    | exact resolve eq14720 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14720
  have eq14810 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14763
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14763
    | exact resolve eq14763 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14763
  have eq14852 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14810
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14810
    | exact resolve eq14810 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14810
  have eq14886 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14852
    | exact resolve eq14852 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14852
  have eq14918 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq14886
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14886
    | exact resolve eq14886 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14886
  have eq14942 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq14918
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq14918
    | exact resolve eq14918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14918
  have eq14950 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq14942
    | exact resolve eq14942 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14942
  have eq16031 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) (M.op (M.op (M.op X3 X4) (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1)) X4)) X2) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)))) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq217 eq619
    | exact resolve eq619 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq16786 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) X2) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16031 X0 X1 X2 X1 X2
       have i₂ := eq14 (M.op (M.op (M.op X0 X1) sF4) X1) X1 X2
       grind)
    | exact superpose eq14 eq16031
    | exact resolve eq16031 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16031
  have eq17950 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) X1) X3) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq217 eq695
    | exact resolve eq695 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq20067 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) = (k (M.op (M.op X1 X0) (M.op (M.op (M.op X2 X3) X1) X3)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq628 X0 X1 X2 X3
       have i₂ := eq632 X0 X1 X2 X3
       grind)
    | exact superpose eq632 eq628
    | exact resolve eq628 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628 eq632
  have eq20328 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1)) = (k (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) X1)) y) := by
    intro X0 X1
    first
    | (have i₁ := eq20067 y x X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20067
    | (have j0 := eq20067 y x X0 X1
       grind)
    | exact resolve eq20067 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51233 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op (σ (M.op x y)) X0) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq709 eq4509
    | exact resolve eq4509 eq709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4509
  have eq51701 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51233 eq4356
    | exact resolve eq4356 eq51233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4356 eq51233
  have eq51814 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51701
  have eq51896 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq51814 eq709
    | exact resolve eq709 eq51814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709 eq51814
  have eq52070 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq51896
  have eq52098 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq52070
       have r₂ := eq603
       grind)
    | exact resolve eq52070 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq52070
  have eq52121 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (M.op (M.op x y) (σ x)) y))) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52098 eq907
    | exact resolve eq907 eq52098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907 eq52098
  have eq52130 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq50 eq52121
    | exact resolve eq52121 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52121
  have eq52634 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ y)) X1)) = (k (M.op (σ y) (M.op (M.op (M.op X0 X1) (σ y)) X1)) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq52130 eq20067
    | exact resolve eq20067 eq52130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20067 eq52130
  have eq52650 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq52634 x x
       have i₂ := eq14 sF3 x x
       grind)
    | exact superpose eq14 eq52634
    | exact resolve eq52634 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52634
  have eq52684 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq52650 eq99
    | exact resolve eq99 eq52650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq52650
  have eq52700 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq52684
  have eq52711 : y = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq52700 eq29
    | exact resolve eq29 eq52700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq52700
  have eq53121 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq52711
    | exact resolve eq52711 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq52711
  have eq53122 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq53121
  have eq53123 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53122 eq20
    | exact resolve eq20 eq53122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53125 : ∀ X0 : G, (M.op X0 (M.op (M.op y X0) y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq53122 eq50
    | exact resolve eq50 eq53122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq53128 : y ≠ y ∨ x = y ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53122 eq113
    | (have r₁ := eq113
       have r₂ := eq53122
       grind)
    | exact resolve eq113 eq53122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq53129 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq53122 eq125
    | exact resolve eq125 eq53122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq53154 : y = (M.op y (M.op y (M.op (M.op y x) y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53122 eq906
    | exact resolve eq906 eq53122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq53157 : ∀ X0 : G, y = (M.op y (M.op (M.op y X0) y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq53122 eq1363
    | exact resolve eq1363 eq53122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363
  have eq53161 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq53162 : x = y ∨ (k y x) = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq53128
  have eq53172 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq53129 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq53129
    | exact resolve eq53129 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq53129
  have eq53176 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53123
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq53123
    | exact resolve eq53123 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53123
  have eq56070 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1304 (M.op (M.op y sF4) y)
       have i₂ := eq53125 sF4
       grind)
    | exact superpose eq53125 eq1304
    | exact resolve eq1304 eq53125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1304
  have eq56404 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ y) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X3)) X1) (σ y)) (M.op (M.op X2 X3) X3)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq56070 eq695
    | exact resolve eq695 eq56070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695 eq56070
  have eq56436 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq56404 x x x x
       have i₂ := eq620 x x sF3 x x
       grind)
    | exact superpose eq620 eq56404
    | exact resolve eq56404 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620 eq56404
  have eq58863 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq53176 eq14950
    | exact resolve eq14950 eq53176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14950
  have eq58873 : (σ (M.op x y)) ≠ (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq58863
       have r₂ := eq27
       grind)
    | exact resolve eq58863 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58863
  have eq60597 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq56436 eq2860
    | exact resolve eq2860 eq56436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860 eq56436
  have eq67471 : (k y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq53162
       have r₂ := eq53161
       grind)
    | exact resolve eq53162 eq53161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53162
  have eq67584 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq67471
       grind)
    | exact superpose eq67471 eq73
    | exact resolve eq73 eq67471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67471
  have eq70024 : y = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53154
       have i₂ := eq53157 x
       grind)
    | exact superpose eq53157 eq53154
    | exact resolve eq53154 eq53157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53154 eq53157
  have eq70132 : y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq70024
  have eq70166 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67584
       have i₂ := eq70132
       grind)
    | exact superpose eq70132 eq67584
    | exact resolve eq67584 eq70132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67584 eq70132
  have eq70275 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq70166
  have eq70302 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq70275
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq70275
    | exact resolve eq70275 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70275
  have eq70477 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70302 eq53172
    | exact resolve eq53172 eq70302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53172 eq70302
  have eq70492 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq70477
  have eq70742 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70492 eq58873
    | exact resolve eq58873 eq70492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58873 eq70492
  have eq70755 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq70742
  have eq70760 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq70755
       have r₂ := eq53176
       grind)
    | exact resolve eq70755 eq53176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53176 eq70755
  have eq70810 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70760 eq60597
    | exact resolve eq60597 eq70760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60597
  have eq70827 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq70810
  have eq70856 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq70827
    | exact resolve eq70827 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70827
  have eq73043 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq70760 eq70856
    | exact resolve eq70856 eq70760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70760 eq70856
  have eq73076 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq73043
  have eq75703 : (τ (σ x)) = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq73076 eq57
    | exact resolve eq57 eq73076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq73076
  have eq75731 : x = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq75703
    | exact resolve eq75703 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq75703
  have eq79648 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq75731
       grind)
    | exact superpose eq75731 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq75731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75731
  have eq79661 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq79648
  have eq1440776 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) X3) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq17950 X0 X1 X2 X3
       have i₂ := eq4506 X0 X1 sF4
       grind)
    | exact superpose eq4506 eq17950
    | exact resolve eq17950 eq4506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4506 eq17950
  have eq1749225 : ∀ X0 X1 : G, x = (M.op x (M.op y (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) y) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y))))) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1440776 X0 X1 x y
       have i₂ := eq79661
       grind)
    | exact superpose eq79661 eq1440776
    | exact resolve eq1440776 eq79661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79661
  have eq1749241 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16786 eq1749225
    | exact resolve eq1749225 eq16786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749225
  have eq1749516 : x = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1749241
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1749241
    | exact resolve eq1749241 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749241
  have eq1749517 : x = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq1749516
  have eq1754596 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53125 x
       have i₂ := eq1749517
       grind)
    | exact superpose eq1749517 eq53125
    | exact resolve eq53125 eq1749517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53125 eq1749517
  have eq1755221 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq1754596
  have eq1755261 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1755221
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1755221
    | exact resolve eq1755221 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755221
  have eq1798792 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq53122 eq1755261
    | exact resolve eq1755261 eq53122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53122 eq1755261
  have eq1799720 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1798792
       have r₂ := eq53161
       grind)
    | exact resolve eq1798792 eq53161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53161 eq1798792
  have eq1799731 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1799720
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1799720
    | exact resolve eq1799720 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1799720
  have eq1799732 : x = (M.op x y) := by grind
  clear eq1799731
  have eq1799734 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1799732 eq20
    | exact resolve eq20 eq1799732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1800102 : ∀ X0 X1 : G, y = (k y (M.op x (M.op (M.op (M.op X0 X1) x) X1))) := by
    intro X0 X1
    first
    | exact superpose eq1799732 eq12744
    | exact resolve eq12744 eq1799732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12744
  have eq1800136 : ∀ X0 X1 : G, (M.op x (M.op (M.op (M.op X0 X1) x) X1)) = (k (M.op x (M.op (M.op (M.op X0 X1) x) X1)) y) := by
    intro X0 X1
    first
    | exact superpose eq1799732 eq20328
    | exact resolve eq20328 eq1799732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20328 eq1799732
  have eq1800236 : x = (k x y) := by
    first
    | (have i₁ := eq1800136 x x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq1800136
    | exact resolve eq1800136 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800136
  have eq1800256 : y = (k y x) := by
    first
    | (have i₁ := eq1800102 x x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq1800102
    | exact resolve eq1800102 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800102
  have eq1800508 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1799734
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1799734
    | exact resolve eq1799734 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799734
  have eq1800690 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1800508 eq26
    | exact resolve eq26 eq1800508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1803342 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1800236
       grind)
    | exact superpose eq1800236 eq44
    | exact resolve eq44 eq1800236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1800236
  have eq1803418 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1800508 eq1803342
    | exact resolve eq1803342 eq1800508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803342
  have eq1803451 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq1803418
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1803418
    | exact resolve eq1803418 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1803418
  have eq1803483 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1800508 eq1803451
    | exact resolve eq1803451 eq1800508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803451
  have eq1803585 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1800256
       grind)
    | exact superpose eq1800256 eq73
    | exact resolve eq73 eq1800256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1803616 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10278 y
       have i₂ := eq1800256
       grind)
    | exact superpose eq1800256 eq10278
    | (have j0 := eq10278 y
       grind)
    | exact resolve eq10278 eq1800256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10278 eq1800256
  have eq1803640 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1803616
  have eq1803664 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1803640
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1803640
    | exact resolve eq1803640 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803640
  have eq1803679 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1800508 eq1803585
    | exact resolve eq1803585 eq1800508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803585
  have eq1803701 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1803664
    | exact resolve eq1803664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803664
  have eq1803716 : (σ y) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1803679
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1803679
    | exact resolve eq1803679 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803679
  have eq1803738 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1803701
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1803701
    | exact resolve eq1803701 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1803701
  have eq1803765 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1803738
    | exact resolve eq1803738 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1803738
  have eq1803787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1800508 eq1803765
    | exact resolve eq1803765 eq1800508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803765
  have eq1803809 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1803787
       have r₂ := eq27
       grind)
    | exact resolve eq1803787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803787
  have eq1803861 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1803809 eq27
    | exact resolve eq27 eq1803809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq1810084 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op X3 X2) (M.op (M.op (M.op (M.op (M.op X4 X5) X6) X5) X3) X6))))) = (M.op (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op X3 X2) (M.op (M.op (M.op (M.op (M.op X4 X5) X6) X5) X3) X6))))) (M.op (M.op (M.op (σ x) (σ y)) X0) (σ y))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq4503 X3 (M.op (M.op X4 X3) (M.op (M.op X5 X4) (M.op (M.op X6 X5) (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X1) X6) X2))))
       have i₂ := eq11746 X0 X1 X2 X3 X4 X5 X6
       grind)
    | exact superpose eq11746 eq4503
    | exact resolve eq4503 eq11746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4503
  have eq1812106 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op X3 X2) (M.op (M.op (M.op (M.op (M.op X4 X5) X6) X5) X3) X6))))) = (M.op (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 X1) (M.op (M.op X3 X2) (M.op (M.op (M.op (M.op (M.op X4 X5) X6) X5) X3) X6))))) (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | exact superpose eq1803809 eq1810084
    | exact resolve eq1810084 eq1803809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810084
  have eq1815312 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ y) X0) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1812106 x x x x X0 x x
       have i₂ := eq11746 X0 x x x x x x
       grind)
    | exact superpose eq11746 eq1812106
    | exact resolve eq1812106 eq11746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11746 eq1812106
  have eq1829295 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1803809 eq1800690
    | exact resolve eq1800690 eq1803809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800690 eq1803809
  have eq2265126 : (σ (k x (k y x))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq1800508 eq9641
    | exact resolve eq9641 eq1800508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9641
  have eq2265127 : (σ (k x (k y x))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq1803716 eq2265126
    | exact resolve eq2265126 eq1803716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265126
  have eq2265128 : (k (σ x) (k (σ y) (σ x))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq2265127
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq2265127
    | exact resolve eq2265127 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2265127
  have eq2265129 : (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq1800508 eq2265128
    | exact resolve eq2265128 eq1800508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265128
  have eq2265130 : (k (σ (M.op x y)) (σ y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq1803716 eq2265129
    | exact resolve eq2265129 eq1803716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265129
  have eq2265131 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ x) = (M.op (k (σ y) (σ x)) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq1803483 eq2265130
    | exact resolve eq2265130 eq1803483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803483 eq2265130
  have eq2265132 : (σ (M.op x y)) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq1800508 eq2265131
    | exact resolve eq2265131 eq1800508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265131
  have eq2265133 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by
    first
    | exact superpose eq1803716 eq2265132
    | exact resolve eq2265132 eq1803716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265132
  have eq2265134 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) ∨ (k (σ y) (σ x)) = (M.op (k (σ y) (σ x)) (σ x)) := by grind
  clear eq2265133
  have eq2265135 : (k (σ y) (σ (M.op x y))) = (M.op (k (σ y) (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1800508 eq2265134
    | exact resolve eq2265134 eq1800508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800508 eq2265134
  have eq2265136 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1803716 eq2265135
    | exact resolve eq2265135 eq1803716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1803716 eq2265135
  have eq2267979 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ y) (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op (σ x) (σ y))) X1) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y))))) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq2265136 eq1440776
    | exact resolve eq1440776 eq2265136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1440776 eq2265136
  have eq2268055 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq16786 eq2267979
    | exact resolve eq2267979 eq16786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16786 eq2267979
  have eq2268591 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1829295 eq2268055
    | exact resolve eq2268055 eq1829295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268055
  have eq2268939 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq2268591
       have r₂ := eq1803861
       grind)
    | exact resolve eq2268591 eq1803861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268591
  have eq2269491 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq2268939 eq1815312
    | exact resolve eq1815312 eq2268939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815312 eq2268939
  have eq2270655 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1829295 eq2269491
    | exact resolve eq2269491 eq1829295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2269491
  have eq2270978 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1829295 eq2270655
    | exact resolve eq2270655 eq1829295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829295 eq2270655
  have eq2271222 : False := by grind
  exact eq2271222

/-- `Equation1265`: `x = x ◇ (((y ◇ z) ◇ y) ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_y_pxy_Equation1265 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1265 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1265.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X1) X3)) = X0 := by
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
  have eq174 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op x y) x) X1)) = X0 := by
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
  have eq175 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X5 : G, (M.op X1 (M.op (M.op X0 X0) X5)) = X1 := by
    intro X0 X1 X5
    first
    | (have i₁ := eq16 X1 X0 (M.op (M.op (M.op x x) x) x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X0 X1 (M.op (M.op (M.op x x) x) x)
       have i₂ := eq16 (M.op (M.op X0 X1) X0) x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : y ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq180 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | exact superpose eq174 eq174
    | exact resolve eq174 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq196 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq183 eq175
    | exact resolve eq175 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq219 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq196 eq176
    | exact resolve eq176 eq196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1047 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
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
  have eq1048 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1064 : (M.op x y) = (k x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq1065 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1185 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1084 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq1084 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq1084 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1084 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1227 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq40
    | exact resolve eq40 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1228 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1227
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1227
    | exact resolve eq1227 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1230 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1228
    | exact resolve eq1228 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228
  have eq1238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1230 eq1065
    | exact resolve eq1065 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq1245 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1238
       have r₂ := eq27
       grind)
    | exact resolve eq1238 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1250 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1245 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1245
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1245
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1245
       grind)
    | exact resolve eq12 eq1245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1245
  have eq1256 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1250
  have eq1261 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1256
    | exact resolve eq1256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1256
  have eq1262 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq1261
  have eq1291 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1262 eq90
    | exact resolve eq90 eq1262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1298 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq1291
    | exact resolve eq1291 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1291
  have eq1301 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1064 eq1298
    | exact resolve eq1298 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1298
  have eq1302 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1301
  have eq1308 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq1302
       grind)
    | exact superpose eq1302 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1302
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq1302
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq1302
       grind)
    | exact resolve eq12 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1311 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1302
       grind)
    | exact superpose eq1302 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1302
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1302
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1302
       grind)
    | exact resolve eq13 eq1302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302
  have eq1313 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1311
  have eq1314 : y = (M.op x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1308
  have eq1316 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1313
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1313
    | exact resolve eq1313 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1319 : y = (M.op x y) ∨ y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1314
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1314
    | exact resolve eq1314 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1320 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1319
  have eq1325 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1316
       grind)
    | exact superpose eq1316 eq39
    | exact resolve eq39 eq1316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1326 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1325
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1325
    | exact resolve eq1325 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1328 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1326
    | exact resolve eq1326 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq1367 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35 y
       have i₂ := eq1320
       grind)
    | exact superpose eq1320 eq35
    | exact resolve eq35 eq1320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320
  have eq1372 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1367
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1367
    | exact resolve eq1367 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1389 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1372 eq1065
    | exact resolve eq1065 eq1372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065 eq1372
  have eq1393 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1389
  have eq1401 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq1393
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq1393
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq1393 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1405 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1393 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1393
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1393
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1393
       grind)
    | exact resolve eq13 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1407 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1405
  have eq1410 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1407
    | exact resolve eq1407 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1413 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq1401
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq1401
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq1401
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq1401 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1414 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1328 eq1410
    | exact resolve eq1410 eq1328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq1410
  have eq1415 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq1413
       have r₂ := eq1048
       grind)
    | exact resolve eq1413 eq1048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048 eq1413
  have eq1416 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1414
       have r₂ := eq27
       grind)
    | exact resolve eq1414 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq1417 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1416 eq27
    | exact resolve eq27 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1419 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1416 eq180
    | (have r₁ := eq180
       have r₂ := eq1416
       grind)
    | exact resolve eq180 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1420 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1416 eq196
    | exact resolve eq196 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq1425 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1419
  have eq2010 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1415 eq107
    | exact resolve eq107 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1415
  have eq2021 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq29 eq2010
    | exact resolve eq2010 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2010
  have eq2042 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq2021 eq1425
    | exact resolve eq1425 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1425
  have eq2043 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq2021 eq1420
    | exact resolve eq1420 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2048 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq2021 eq178
    | exact resolve eq178 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2052 : ∀ X0 : G, x = (k y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq2043 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043
  have eq2053 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k y x) := by grind
  clear eq2042
  have eq2056 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) ∨ x = (k y x) := by
    intro X0
    first
    | exact superpose eq26 eq2048
    | (have j0 := eq2048 X0
       grind)
    | exact resolve eq2048 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2048
  have eq2063 : ∀ X0 : G, x = (k y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq1416 eq2056
    | exact resolve eq2056 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056
  have eq2084 : ∀ X0 : G, (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq36 x
       have i₂ := eq2052 X0
       grind)
    | exact superpose eq2052 eq36
    | (have j1 := eq2052 X0
       grind)
    | exact resolve eq36 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2086 : ∀ X0 : G, x ≠ x ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1140 y x
       have i₂ := eq2052 X0
       grind)
    | exact superpose eq2052 eq1140
    | (have j0 := eq1140 y x
       have j1 := eq2052 X0
       grind)
    | (have r₁ := eq1140 y x
       have r₂ := eq2052 X0
       grind)
    | exact resolve eq1140 eq2052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2087 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq2086 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2086
  have eq2090 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2087 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2087
    | (have j0 := eq2087 X0
       grind)
    | exact resolve eq2087 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2091 : ∀ X0 : G, x = (M.op y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq2090 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090
  have eq2093 : ∀ X0 : G, (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2084 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2084
    | (have j0 := eq2084 X0
       grind)
    | exact resolve eq2084 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq2108 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op x y) ∨ x = (k y x) := by
    first
    | exact superpose eq2053 eq152
    | exact resolve eq152 eq2053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2053
  have eq2120 : x = (k y x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq2108
    | exact resolve eq2108 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108
  have eq2130 : ∀ X0 : G, x ≠ x ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1140 y x
       have i₂ := eq2063 X0
       grind)
    | exact superpose eq2063 eq1140
    | (have j0 := eq1140 y x
       have j1 := eq2063 X0
       grind)
    | (have r₁ := eq1140 y x
       have r₂ := eq2063 X0
       grind)
    | exact resolve eq1140 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063
  have eq2131 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq2130 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2130
  have eq2134 : ∀ X0 : G, y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2131 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2131
    | (have j0 := eq2131 X0
       grind)
    | exact resolve eq2131 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2131
  have eq2135 : ∀ X0 : G, x = (M.op y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq2134 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134
  have eq2190 : ∀ X0 : G, x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2091 X0
       grind)
    | exact superpose eq2091 eq13
    | (have j0 := eq13 y x
       have j1 := eq2091 X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2091 X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2091 X0
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq2091 (σ x)
       grind)
    | exact resolve eq13 eq2091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2195 : ∀ X0 : G, (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq2190 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2190
  have eq2201 : ∀ X0 : G, (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2195 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2195
    | (have j0 := eq2195 X0
       grind)
    | exact resolve eq2195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2231 : x ≠ x ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1140 y x
       have i₂ := eq2120
       grind)
    | exact superpose eq2120 eq1140
    | (have j0 := eq1140 y x
       grind)
    | (have r₁ := eq1140 y x
       have r₂ := eq2120
       grind)
    | exact resolve eq1140 eq2120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2120
  have eq2232 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq2231
  have eq2235 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2232
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2232
    | exact resolve eq2232 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232
  have eq2236 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by grind
  clear eq2235
  have eq2239 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1064 eq2236
    | exact resolve eq2236 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064 eq2236
  have eq2242 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq2239
       grind)
    | exact superpose eq2239 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2239
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2239
       grind)
    | exact resolve eq12 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2243 : x ≠ x ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2239
       grind)
    | exact superpose eq2239 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2239
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2239
       grind)
    | exact resolve eq13 eq2239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq2248 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2243
  have eq2249 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2242
  have eq2254 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2248
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2248
    | exact resolve eq2248 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248
  have eq2255 : y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2249
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2249
    | exact resolve eq2249 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249
  have eq2256 : y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2255
  have eq2315 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2052 X0
       have i₂ := eq2254
       grind)
    | exact superpose eq2254 eq2052
    | (have j0 := eq2052 X0
       grind)
    | exact resolve eq2052 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2052
  have eq2319 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2315 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2315
  have eq2386 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2319 eq2021
    | exact resolve eq2021 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021 eq2319
  have eq2401 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq2386
  have eq2412 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2254 eq2401
    | exact resolve eq2401 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2413 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2412
  have eq2417 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2413 eq31
    | exact resolve eq31 eq2413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2420 : (k x y) = (τ (k (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2413 eq98
    | exact resolve eq98 eq2413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq2422 : (k y x) = (τ (k (σ x) (σ x))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2413 eq114
    | exact resolve eq114 eq2413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq2413
  have eq2473 : (k x x) = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97 eq2422
    | exact resolve eq2422 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422
  have eq2475 : (k x x) = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97 eq2420
    | exact resolve eq2420 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq2420
  have eq2478 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq2417
    | exact resolve eq2417 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417
  have eq2480 : (M.op x y) = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2254 eq2473
    | exact resolve eq2473 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254 eq2473
  have eq2481 : y = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2256 eq2475
    | exact resolve eq2475 eq2256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256 eq2475
  have eq2483 : x = (k x x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2478 eq2481
    | exact resolve eq2481 eq2478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2478 eq2481
  have eq2484 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2480 eq2483
    | exact resolve eq2483 eq2480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480 eq2483
  have eq2485 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2484
  have eq2486 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2485
       grind)
    | exact superpose eq2485 eq18
    | exact resolve eq18 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3390 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = X0 ∨ y = (M.op x y) ∨ (M.op X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq178 y x X0
       have i₂ := eq2135 X1
       grind)
    | exact superpose eq2135 eq178
    | (have j1 := eq2135 X1
       grind)
    | exact resolve eq178 eq2135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq2135
  have eq3396 : ∀ X0 X1 : G, (M.op X1 (σ y)) = X1 ∨ y = (M.op x y) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3390 X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3390
    | (have j0 := eq3390 X0 X1
       grind)
    | exact resolve eq3390 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390
  have eq3666 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq39 y
       have i₂ := eq2201 X0
       grind)
    | (have i₁ := eq39 X0
       have i₂ := eq2201 (k X0 x)
       grind)
    | exact superpose eq2201 eq39
    | (have j1 := eq2201 X0
       grind)
    | exact resolve eq39 eq2201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2201
  have eq3678 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3666 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3666
    | (have j0 := eq3666 X0
       grind)
    | exact resolve eq3666 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3666
  have eq3680 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq3678
    | (have j0 := eq3678 X0
       grind)
    | exact resolve eq3678 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3678
  have eq3682 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2093 eq3680
    | (have j0 := eq3680 X0
       have j1 := eq2093 X0
       grind)
    | exact resolve eq3680 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093 eq3680
  have eq3737 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq3682 eq1420
    | exact resolve eq1420 eq3682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3682
  have eq3748 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq3737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3737
  have eq3814 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3748 eq26
    | (have j1 := eq3748 (σ x)
       grind)
    | exact resolve eq26 eq3748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3748
  have eq3832 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3814 eq1416
    | exact resolve eq1416 eq3814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3814
  have eq3833 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq3832
  have eq3838 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq3833 eq31
    | exact resolve eq31 eq3833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3833
  have eq3906 : x = y ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq3838
    | exact resolve eq3838 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3838
  have eq3917 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2485 eq3906
    | exact resolve eq3906 eq2485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2485 eq3906
  have eq3918 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq3917
  have eq3931 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3918 eq1417
    | exact resolve eq1417 eq3918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1417
  have eq3939 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq3931
  have eq4461 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq26
       have i₂ := eq3396 (M.op sF2 sF3) x
       grind)
    | exact superpose eq3396 eq26
    | (have j1 := eq3396 X0 (σ x)
       grind)
    | exact resolve eq26 eq3396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396
  have eq4469 : ∀ X0 : G, (σ x) = (σ y) ∨ y = (M.op x y) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq1416 eq4461
    | (have j0 := eq4461 X0
       grind)
    | exact resolve eq4461 eq1416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4461
  have eq4472 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4469 X0
       grind)
    | (have r₁ := eq4469 X0
       have r₂ := eq3939
       grind)
    | exact resolve eq4469 eq3939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4469
  have eq4484 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4472 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq4472 (M.op x y)
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4472 X0
       grind)
    | exact resolve eq13 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5604 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq4484 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4484
  have eq5605 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4472 eq5604
    | exact resolve eq5604 eq4472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4472 eq5604
  have eq5607 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5605 eq41
    | exact resolve eq41 eq5605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq5605
  have eq5619 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq5607
    | exact resolve eq5607 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5607
  have eq5621 : (σ x) = (k (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3918 eq5619
    | exact resolve eq5619 eq3918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3918 eq5619
  have eq5630 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5621 eq1140
    | (have j0 := eq1140 (σ x) (σ x)
       grind)
    | (have r₁ := eq1140 (σ x) (σ x)
       have r₂ := eq5621
       grind)
    | exact resolve eq1140 eq5621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5621
  have eq5631 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq5630
  have eq5632 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq5631
  have eq5647 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5632 eq219
    | exact resolve eq219 eq5632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq5632
  have eq5724 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5647 eq1420
    | exact resolve eq1420 eq5647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420 eq5647
  have eq5737 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5724
  have eq5820 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5737 eq26
    | (have j1 := eq5737 (σ x)
       grind)
    | exact resolve eq26 eq5737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5737
  have eq5847 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5820 eq1416
    | exact resolve eq1416 eq5820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1416 eq5820
  have eq5848 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq5847
  have eq5852 : y = (M.op x y) := by
    first
    | (have r₁ := eq5848
       have r₂ := eq3939
       grind)
    | exact resolve eq5848 eq3939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3939 eq5848
  have eq5855 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5852
       grind)
    | exact superpose eq5852 eq18
    | exact resolve eq18 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq5856 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5852
       grind)
    | exact superpose eq5852 eq24
    | exact resolve eq24 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq5857 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq5852
       grind)
    | exact superpose eq5852 eq36
    | exact resolve eq36 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq5858 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq5852
       grind)
    | exact superpose eq5852 eq40
    | exact resolve eq40 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq5859 : (M.op x y) ≠ (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq179
       have i₂ := eq5852
       grind)
    | exact superpose eq5852 eq179
    | (have r₁ := eq179
       have r₂ := eq5852
       grind)
    | exact resolve eq179 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq5860 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq1047
       have i₂ := eq5852
       grind)
    | exact superpose eq5852 eq1047
    | (have r₁ := eq1047
       have r₂ := eq5852
       grind)
    | exact resolve eq1047 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1047
  have eq5862 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq5860
  have eq5863 : (k x (M.op x y)) = (M.op (M.op x y) x) := by grind
  clear eq5859
  have eq6234 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq5856 eq20
    | exact resolve eq20 eq5856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6330 : ∀ X0 : G, (M.op X0 (k x (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq5863 eq183
    | exact resolve eq183 eq5863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6338 : x ≠ (k x (M.op x y)) ∨ (k (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq5863 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | exact resolve eq13 eq5863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6348 : x ≠ (k x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) x) := by
    first
    | exact superpose eq5855 eq6338
    | exact resolve eq6338 eq5855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5855 eq6338
  have eq7490 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq5862 eq5857
    | exact resolve eq5857 eq5862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5857 eq5862
  have eq7502 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq7490
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7490
    | exact resolve eq7490 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7490
  have eq7505 : (σ x) = (k (σ y) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq5863 eq7502
    | exact resolve eq7502 eq5863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7502
  have eq7527 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq7505 eq1185
    | (have j0 := eq1185 (σ y) (σ x)
       grind)
    | (have r₁ := eq1185 (σ y) (σ x)
       have r₂ := eq7505
       grind)
    | exact resolve eq1185 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7528 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq7505 eq1140
    | (have j0 := eq1140 (σ y) (σ x)
       grind)
    | (have r₁ := eq1140 (σ y) (σ x)
       have r₂ := eq7505
       grind)
    | exact resolve eq1140 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140 eq7505
  have eq7529 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k x (M.op x y)) := by grind
  clear eq7528
  have eq7530 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq7527
  have eq7531 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq26 eq7529
    | exact resolve eq7529 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7529
  have eq7532 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq26 eq7530
    | exact resolve eq7530 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7530
  have eq7538 : x = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq7532
    | exact resolve eq7532 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7532
  have eq7886 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7538 eq6330
    | exact resolve eq6330 eq7538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7890 : x ≠ x ∨ (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7538 eq6348
    | (have r₁ := eq6348
       have r₂ := eq7538
       grind)
    | exact resolve eq6348 eq7538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6348
  have eq7892 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7538 eq5858
    | exact resolve eq5858 eq7538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5858 eq7538
  have eq7898 : (M.op x y) = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7890
  have eq7903 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7892
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7892
    | exact resolve eq7892 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7892
  have eq7989 : (M.op x y) = (k x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5863
       have i₂ := eq7886 sF0
       grind)
    | exact superpose eq7886 eq5863
    | exact resolve eq5863 eq7886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5863 eq7886
  have eq8026 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7898 eq39
    | exact resolve eq39 eq7898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq7898
  have eq8037 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8026
    | exact resolve eq8026 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8026
  have eq8048 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6234 eq8037
    | exact resolve eq8037 eq6234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8037
  have eq8364 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7989 eq35
    | exact resolve eq35 eq7989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq7989
  have eq8376 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq8364
    | exact resolve eq8364 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8364
  have eq8379 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6234 eq8376
    | exact resolve eq8376 eq6234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8376
  have eq8382 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq7903 eq8379
    | exact resolve eq8379 eq7903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7903 eq8379
  have eq8386 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq8382 eq27
    | exact resolve eq27 eq8382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8404 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq8386
       have r₂ := eq6234
       grind)
    | exact resolve eq8386 eq6234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8386
  have eq8452 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8048 eq1185
    | (have j0 := eq1185 (σ y) (σ x)
       grind)
    | exact resolve eq1185 eq8048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185 eq8048
  have eq8454 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8452
  have eq8461 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8454
       have r₂ := eq8382
       grind)
    | exact resolve eq8454 eq8382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8382 eq8454
  have eq8466 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq8461
    | exact resolve eq8461 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461
  have eq8467 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8466
  have eq8472 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8404 eq8467
    | exact resolve eq8467 eq8404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8404 eq8467
  have eq8473 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8472
  have eq8480 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8473 eq27
    | exact resolve eq27 eq8473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq8491 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq6234 eq8480
    | exact resolve eq8480 eq6234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6234 eq8480
  have eq11865 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq7531 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7531
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7531
       grind)
    | exact resolve eq12 eq7531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7531
  have eq11878 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq11865
  have eq11889 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq26 eq11878
    | exact resolve eq11878 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq11878
  have eq11890 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by grind
  clear eq11889
  have eq11901 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq8473 eq11890
    | exact resolve eq11890 eq8473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8473 eq11890
  have eq11911 : (σ y) = (k (σ x) (σ y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have r₁ := eq11901
       have r₂ := eq8491
       grind)
    | exact resolve eq11901 eq8491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11901
  have eq11955 : (τ (σ y)) = (k x (τ (σ y))) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq11911 eq90
    | exact resolve eq90 eq11911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq11911
  have eq11969 : y = (k x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq31 eq11955
    | exact resolve eq11955 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq11955
  have eq11974 : (M.op x y) = (k x (M.op x y)) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq11969
       have i₂ := eq5852
       grind)
    | exact superpose eq5852 eq11969
    | exact resolve eq11969 eq5852
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5852 eq11969
  have eq12027 : ∀ X0 : G, x = (k x (M.op x y)) ∨ (M.op X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq11974 eq6330
    | exact resolve eq6330 eq11974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11974
  have eq12626 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = X1 ∨ (M.op X0 x) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6330 X0
       have i₂ := eq12027 (k x sF0)
       grind)
    | exact superpose eq12027 eq6330
    | (have j1 := eq12027 X1
       grind)
    | exact resolve eq6330 eq12027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6330 eq12027
  have eq12841 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq2486
       have i₂ := eq12626 (M.op x sF0) x
       grind)
    | exact superpose eq12626 eq2486
    | (have j1 := eq12626 X0 x
       grind)
    | exact resolve eq2486 eq12626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12626
  have eq12858 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12841 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12841
  have eq12956 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq183 X0
       have i₂ := eq12858 sF0
       grind)
    | exact superpose eq12858 eq183
    | exact resolve eq183 eq12858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq12858
  have eq13064 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12956 eq2486
    | exact resolve eq2486 eq12956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2486 eq12956
  have eq13085 : x = (M.op x y) := by grind
  clear eq13064
  have eq13100 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq13085
       grind)
    | exact superpose eq13085 eq22
    | exact resolve eq22 eq13085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq13085
  have eq13177 : (σ x) = (σ y) := by
    first
    | exact superpose eq13100 eq5856
    | exact resolve eq5856 eq13100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5856 eq13100
  have eq13224 : False := by grind
  exact eq13224

/-- `Equation1434`: `x = (x ◇ x) ◇ (y ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation1434 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq67 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq15
    | exact resolve eq15 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq75 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq75
    | exact resolve eq75 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq75
  have eq100 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq103 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq100 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq100
    | exact resolve eq100 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    grind
  clear eq103
  have eq202 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq207 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq202
    | (have j0 := eq202 X0 X1
       grind)
    | exact resolve eq202 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq1048 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq204
    | exact resolve eq204 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq1098 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1048 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1048
    | (have j0 := eq1048 X0 X1
       grind)
    | exact resolve eq1048 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq3628 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq207 x y
       grind)
    | exact superpose eq207 eq16
    | (have j1 := eq207 x y
       grind)
    | exact resolve eq16 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq5421 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3628
       have i₂ := eq1098 y x
       grind)
    | exact superpose eq1098 eq3628
    | (have j1 := eq1098 (σ y) (σ (M.op x x))
       grind)
    | (have r₁ := eq3628
       have r₂ := eq1098 y x
       grind)
    | (have r₁ := eq3628
       have r₂ := eq1098 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3628
       have r₂ := eq1098 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3628 eq1098
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1098 eq3628
  have eq5422 : x = y ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq5421
  have eq5424 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5422
       grind)
    | exact superpose eq5422 eq16
    | exact resolve eq16 eq5422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5422
  have eq5425 : y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5424
       have r₂ := eq82 x
       grind)
    | exact resolve eq5424 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5424
  have eq5434 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq106 x
       have i₂ := eq5425
       grind)
    | exact superpose eq5425 eq106
    | exact resolve eq106 eq5425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5425
  have eq5456 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5434
       have r₂ := eq16
       grind)
    | exact resolve eq5434 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5434
  have eq5460 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5456
       grind)
    | exact superpose eq5456 eq10
    | exact resolve eq10 eq5456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5456
  have eq5513 : x = y ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq5460
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5460
    | exact resolve eq5460 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5460
  have eq5516 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5513
       grind)
    | exact superpose eq5513 eq16
    | exact resolve eq16 eq5513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5513
  have eq5517 : (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq5516
       have r₂ := eq82 x
       grind)
    | exact resolve eq5516 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq5516
  have eq5529 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5517
       grind)
    | exact superpose eq5517 eq10
    | exact resolve eq10 eq5517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5517
  have eq5582 : y = (M.op x x) := by
    first
    | (have i₁ := eq5529
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5529
    | exact resolve eq5529 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5529
  have eq5595 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106 x
       have i₂ := eq5582
       grind)
    | exact superpose eq5582 eq106
    | exact resolve eq106 eq5582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq5582
  have eq5617 : False := by grind
  exact eq5617
